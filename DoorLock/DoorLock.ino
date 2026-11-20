/*
 * BLE-замок на ESP32 + реле SRD-05VDC-SL-C + управление по Bluetooth   v5.0
 *
 * Требования:
 *   - Плата: ESP32 (пакет Espressif), "ESP32 Dev Module"
 *   - Tools → Partition Scheme → "Minimal SPIFFS (1.9MB APP with OTA/190KB SPIFFS)"
 *   - Библиотека NimBLE-Arduino (h2zero) ВЕРСИИ 1.4.x  (с 2.x не соберётся!)
 *
 * Управление (добавление телефонов, калибровка, настройки, Wi-Fi) — страницей
 * doorlock-control.html по Bluetooth (Chrome на Android).
 * Wi-Fi выключен; включается на 10 с при старте, командой по Bluetooth,
 * коротким удержанием BOOT (2–7 с) или удержанием кнопки выхода 5 с. Нужен только для обновления прошивки:
 * подключиться к точке ESP32 → http://192.168.4.1
 * Короткое нажатие BOOT (<2 с) — окно добавления телефона (90 с).
 * Удержание BOOT 10 с — сброс сетевых настроек и паролей (телефоны сохраняются).
 */
#include <Arduino.h>
#include <WiFi.h>
#include <WebServer.h>
#include <ESPmDNS.h>
#include <Update.h>
#include <Preferences.h>
#include <NimBLEDevice.h>
#include <NimBLEHIDDevice.h>
#include "esp_bt.h"
#include "esp_system.h"
#include "esp_partition.h"
#include "esp_spi_flash.h"
#include <sys/time.h>
#include <time.h>
#include <stdarg.h>

// ============== ЗНАЧЕНИЯ ПО УМОЛЧАНИЮ (меняются в веб-панели) ==============
#define FW_VERSION     "5.2"
#define DEF_AP_SSID    "DoorLock-ESP32"
#define DEF_AP_PASS    "Zamok-7294-Dver"
#define DEF_WEB_USER   "admin"
#define DEF_WEB_PASS   "pass"
#define DEF_BLE_NAME   "Door-Lock"
#define DEF_RELAY_LOW  false        // false = реле срабатывает от HIGH, true = от LOW
#define MDNS_NAME      "doorlock"   // http://doorlock.local
#define DEF_PIN        0            // PIN сопряжения по умолчанию = 000000 (смените в настройках!)

// ============== ПИНЫ ==============
#define RELAY_PIN      26   // -> IN модуля реле (или база транзистора через 1 кОм)
#define LED_PIN         2   // встроенный светодиод
#define BUTTON_PIN     27   // кнопка выхода на GND (необязательно)
#define BOOT_BTN_PIN    0   // кнопка BOOT на плате

#define PAIR_WINDOW_MS     90000UL
#define AUTH_TIMEOUT_MS    20000UL
#define NET_RESET_HOLD_MS  10000UL
#define WIFI_BTN_HOLD_MS    5000UL   // удержание кнопки выхода — включить Wi-Fi

#define MAX_DEVICES  CONFIG_BT_NIMBLE_MAX_BONDS
#define MAX_SLOTS    9
#define LOG_SIZE     20

struct Cfg { String apSsid, apPass, webUser, webPass, bleName, staSsid, staPass; bool relayLow; };
struct DevRec { uint8_t addr[6]; uint8_t type; char name[32]; uint8_t blocked; uint32_t blockUntil; };
#define RSSI_WIN 10      // окно сглаживания: 10 измерений по 100 мс = 1 секунда
struct DevRt  { bool present; bool opened; bool everSeen; uint32_t lastDisc; uint16_t conn; int8_t rssi; uint32_t nearMs;
                int8_t raw; int8_t hist[RSSI_WIN]; uint8_t hn, hi; uint32_t aboveSince; };
struct Slot   { bool used; uint16_t handle; uint32_t since; bool authed; int8_t dev; bool pending; uint32_t authAt; };
enum EvType : uint8_t { EV_CONNECT, EV_AUTH, EV_DISC };
struct BleEvent { EvType type; uint16_t conn; ble_addr_t id; bool enc; bool authn; };
struct LogRec { uint32_t ms; char text[96]; };
struct Cmd { uint16_t conn; char text[128]; };

Cfg cfg;
DevRec devs[MAX_DEVICES];
DevRt  rt[MAX_DEVICES];
uint8_t devCount = 0;
Slot   slots[MAX_SLOTS];
LogRec logs[LOG_SIZE];
uint8_t logHead = 0, logCount = 0;

QueueHandle_t evQueue;
Preferences prefs;
WebServer server(80);
NimBLEServer* pServer = nullptr;

int8_t   rssiThr  = -65;   // уровень "у двери" по умолчанию (для телефонов без записи)
uint8_t  awayHyst = 6;     // насколько слабее уровня считать "ушёл"
int8_t   devLevel[MAX_DEVICES];  // записанный уровень "у двери" для каждого телефона (0 = нет)
uint16_t rearmSec = 120;
uint16_t pulseMs  = 2000;
uint16_t graceSec = 60;
uint16_t confirmMs = 1000;  // сигнал должен держаться выше порога столько мс    // не открывать N секунд после включения
uint8_t  txLevel  = 0;     // 0 = -12 дБм (минимум) ... 7 = +9 дБм

volatile uint32_t pairPin = 0;
uint32_t storedPin = DEF_PIN;
uint32_t wifiLimit = 0;
bool wifiBootWin = false;
bool otaNoSlots = false;   // схема разделов без второго OTA-раздела — обновление по воздуху невозможно
volatile bool otaBusy = false;   // идёт обновление прошивки: Bluetooth отключён, чтобы не мешал записи
String respStr, lastMsg;   // ответ по Bluetooth и сообщение о результате последней команды
uint32_t pairUntil = 0;
bool relayActive = false;
uint32_t relayStart = 0;
bool timeValid = false;
uint32_t rebootAt = 0;
bool otaAuthOk = false;
bool wifiOn = false;
uint32_t lastActivity = 0;
uint16_t woffSec = 60;     // выключать Wi-Fi без подключений через N секунд (0 = никогда)

static const uint8_t HID_MAP[] = {
  0x05, 0x0C, 0x09, 0x01, 0xA1, 0x01, 0x85, 0x01,
  0x15, 0x00, 0x25, 0x01, 0x75, 0x01, 0x95, 0x02,
  0x09, 0xE9, 0x09, 0xEA, 0x81, 0x02,
  0x95, 0x06, 0x81, 0x03, 0xC0
};

// ---------------------- утилиты ----------------------
void logEv(const char* fmt, ...) {
  LogRec& r = logs[logHead];
  va_list ap; va_start(ap, fmt);
  vsnprintf(r.text, sizeof(r.text), fmt, ap);
  va_end(ap);
  r.ms = millis();
  logHead = (logHead + 1) % LOG_SIZE;
  if (logCount < LOG_SIZE) logCount++;
  Serial.println(r.text);
}

String addrStr(const uint8_t* a) {
  char b[18];
  snprintf(b, sizeof(b), "%02x:%02x:%02x:%02x:%02x:%02x", a[5], a[4], a[3], a[2], a[1], a[0]);
  return String(b);
}

bool parseAddr(const String& s, uint8_t* out) {
  unsigned int b[6];
  if (sscanf(s.c_str(), "%x:%x:%x:%x:%x:%x", &b[0], &b[1], &b[2], &b[3], &b[4], &b[5]) != 6) return false;
  for (int i = 0; i < 6; i++) out[5 - i] = (uint8_t)b[i];
  return true;
}

void safeCopy(char* dst, size_t cap, const char* src) {
  size_t n = 0;
  while (src[n] && n < cap - 1) n++;
  if (src[n]) while (n > 0 && ((uint8_t)src[n] & 0xC0) == 0x80) n--;
  memcpy(dst, src, n); dst[n] = 0;
  for (size_t i = 0; i < n; i++) {
    char c = dst[i];
    if (c == '"' || c == '\\' || c == '<' || c == '>' || (uint8_t)c < 0x20) dst[i] = '_';
  }
}

String jsEsc(const char* s) {
  String o;
  for (; *s; s++) {
    char c = *s;
    if (c == '"' || c == '\\') { o += '\\'; o += c; }
    else if ((uint8_t)c < 0x20) o += ' ';
    else o += c;
  }
  return o;
}

int findDev(const uint8_t* a) {
  for (int i = 0; i < devCount; i++) if (memcmp(devs[i].addr, a, 6) == 0) return i;
  return -1;
}

// ---------------------- хранение ----------------------
void loadCfg() {
  cfg.apSsid   = prefs.getString("ap_ssid", DEF_AP_SSID);
  cfg.apPass   = prefs.getString("ap_pass", DEF_AP_PASS);
  cfg.webUser  = prefs.getString("w_user",  DEF_WEB_USER);
  cfg.webPass  = prefs.getString("w_pass",  DEF_WEB_PASS);
  cfg.bleName  = prefs.getString("ble",     DEF_BLE_NAME);
  cfg.staSsid  = prefs.getString("sta_ssid", "");
  cfg.staPass  = prefs.getString("sta_pass", "");
  cfg.relayLow = prefs.getBool("rlow", DEF_RELAY_LOW);
  woffSec      = prefs.getUShort("woff", 60);
  if (woffSec < 30 || woffSec > 3600) woffSec = 60;   // Wi-Fi всегда должен выключаться сам
}

void saveDevs() {
  prefs.putUChar("cnt", devCount);
  if (devCount) prefs.putBytes("devs", devs, sizeof(DevRec) * devCount);
}

void saveLevels() { prefs.putBytes("lvls", devLevel, sizeof(devLevel)); }
int8_t levelOf(int i) { return devLevel[i] ? devLevel[i] : rssiThr; }

void saveSettings() {
  prefs.putChar("rssi", rssiThr);
  prefs.putUShort("rearm", rearmSec);
  prefs.putUShort("pulse", pulseMs);
  prefs.putUChar("tx", txLevel);
  prefs.putUShort("grace", graceSec);
  prefs.putUChar("hyst", awayHyst);
  prefs.putUShort("conf", confirmMs);
}

void loadAll() {
  devCount = prefs.getUChar("cnt", 0);
  if (devCount > MAX_DEVICES) devCount = MAX_DEVICES;
  if (devCount && prefs.getBytes("devs", devs, sizeof(DevRec) * devCount) != sizeof(DevRec) * devCount) devCount = 0;
  rssiThr  = prefs.getChar("rssi", -65);
  rearmSec = prefs.getUShort("rearm", 120);
  pulseMs  = prefs.getUShort("pulse", 2000);
  txLevel  = prefs.getUChar("tx", 0);
  graceSec = prefs.getUShort("grace", 60);
  awayHyst = prefs.getUChar("hyst", 6);
  if (prefs.getBytes("lvls", devLevel, sizeof(devLevel)) != sizeof(devLevel)) memset(devLevel, 0, sizeof(devLevel));
  confirmMs = prefs.getUShort("conf", 1000);
  if (txLevel > 7) txLevel = 0;
  storedPin = prefs.getUInt("pin", DEF_PIN);
  if (storedPin > 999999) storedPin = DEF_PIN;
  for (int i = 0; i < MAX_DEVICES; i++) { rt[i] = {}; rt[i].conn = 0xFFFF; }
}

void resetNetCfg() {
  const char* keys[] = { "ap_ssid", "ap_pass", "w_user", "w_pass", "sta_ssid", "sta_pass" };
  for (auto k : keys) if (prefs.isKey(k)) prefs.remove(k);
  logEv("Сетевые настройки и пароли сброшены (кнопка BOOT)");
  rebootAt = millis() + 500;
}

// ---------------------- BLE bonds ----------------------
void removeBond(const uint8_t* a) {
  for (int i = NimBLEDevice::getNumBonds() - 1; i >= 0; i--) {
    NimBLEAddress b = NimBLEDevice::getBondedAddress(i);
    if (memcmp(b.getNative(), a, 6) == 0) NimBLEDevice::deleteBond(b);
  }
}

void cleanupBonds() {
  for (int i = NimBLEDevice::getNumBonds() - 1; i >= 0; i--) {
    NimBLEAddress b = NimBLEDevice::getBondedAddress(i);
    if (findDev(b.getNative()) < 0) NimBLEDevice::deleteBond(b);
  }
}

// мощность передатчика BLE: реклама, новые и текущие соединения
void applyTxPower() {
  esp_power_level_t lvl = (esp_power_level_t)txLevel;
  for (int t = ESP_BLE_PWR_TYPE_CONN_HDL0; t <= ESP_BLE_PWR_TYPE_DEFAULT; t++)
    esp_ble_tx_power_set((esp_ble_power_type_t)t, lvl);
}

bool pairingActive() { return pairUntil != 0 && (int32_t)(pairUntil - millis()) > 0; }

void newPin() {
  pairPin = storedPin;
  NimBLEDevice::setSecurityPasskey(pairPin);
}

bool isBlocked(int i) {
  DevRec& d = devs[i];
  if (d.blocked) return true;
  if (d.blockUntil) {
    if (!timeValid) return true;
    if ((uint32_t)time(nullptr) < d.blockUntil) return true;
    d.blockUntil = 0; saveDevs();
  }
  return false;
}

// ---------------------- реле ----------------------
void relayOut(bool on) {
  bool lvl = cfg.relayLow ? !on : on;
  digitalWrite(RELAY_PIN, lvl ? HIGH : LOW);
}

void initRelayPin() {
  // для модулей с управлением по LOW — открытый сток: в покое линия отпущена
  pinMode(RELAY_PIN, cfg.relayLow ? OUTPUT_OPEN_DRAIN : OUTPUT);
  relayOut(relayActive);
}

void openDoor(const char* who) {
  static uint32_t lastOpen = 0;
  if (relayActive) return;
  if (lastOpen && millis() - lastOpen < 3000) return;   // не чаще раза в 3 с
  lastOpen = millis();
  relayActive = true; relayStart = millis();
  relayOut(true);
  logEv("ОТКРЫТО: %s", who);
}

// ---------------------- BLE колбэки ----------------------
class SrvCb : public NimBLEServerCallbacks {
  void onConnect(NimBLEServer* s, ble_gap_conn_desc* d) override {
    BleEvent e = {}; e.type = EV_CONNECT; e.conn = d->conn_handle; e.id = d->peer_id_addr;
    xQueueSend(evQueue, &e, 0);
    NimBLEDevice::startSecurity(d->conn_handle);
    if (!otaBusy && s->getConnectedCount() < CONFIG_BT_NIMBLE_MAX_CONNECTIONS) NimBLEDevice::startAdvertising();
  }
  void onDisconnect(NimBLEServer* s, ble_gap_conn_desc* d) override {
    BleEvent e = {}; e.type = EV_DISC; e.conn = d->conn_handle; e.id = d->peer_id_addr;
    xQueueSend(evQueue, &e, 0);
  }
  uint32_t onPassKeyRequest() override { return pairPin; }
  bool onConfirmPIN(uint32_t) override { return false; }
  void onAuthenticationComplete(ble_gap_conn_desc* d) override {
    BleEvent e = {}; e.type = EV_AUTH; e.conn = d->conn_handle; e.id = d->peer_id_addr;
    e.enc = d->sec_state.encrypted; e.authn = d->sec_state.authenticated;
    xQueueSend(evQueue, &e, 0);
  }
};

Slot* getSlot(uint16_t h, bool create) {
  for (auto& s : slots) if (s.used && s.handle == h) return &s;
  if (!create) return nullptr;
  for (auto& s : slots) if (!s.used) { s = {}; s.used = true; s.handle = h; s.since = millis(); s.dev = -1; return &s; }
  return nullptr;
}

void handleEvent(const BleEvent& e) {
  uint32_t now = millis();
  if (e.type == EV_CONNECT) { getSlot(e.conn, true); return; }

  if (e.type == EV_DISC) {
    Slot* s = getSlot(e.conn, false);
    if (s) {
      if (s->dev >= 0) {
        DevRt& r = rt[s->dev];
        r.present = false; r.lastDisc = now; r.conn = 0xFFFF;
        logEv("%s: вне зоны", devs[s->dev].name);
      }
      s->used = false;
    }
    return;
  }

  Slot* s = getSlot(e.conn, true);
  if (!s) return;
  if (!e.enc || !e.authn) {
    logEv("Отклонено %s: шифрование %s, проверка PIN %s", addrStr(e.id.val).c_str(),
          e.enc ? "да" : "НЕТ", e.authn ? "да" : "НЕТ");
    pServer->disconnect(e.conn);
    return;
  }
  // Настоящий (постоянный) адрес телефона приходит ПОСЛЕ включения шифрования,
  // поэтому решение принимаем чуть позже — в checkPending().
  if (!s->authed) { s->pending = true; s->authAt = now; }
}

bool isRpa(const ble_addr_t& a) {
  return a.type == BLE_ADDR_RANDOM && (a.val[5] & 0xC0) == 0x40;
}

void processAuth(Slot* s, const ble_addr_t& id) {
  uint32_t now = millis();
  int i = findDev(id.val);
  bool fresh = false;
  if (i < 0) {
    if (pairingActive() && devCount < MAX_DEVICES) {
      i = devCount++;
      DevRec& d = devs[i];
      memset(&d, 0, sizeof(d));
      memcpy(d.addr, id.val, 6);
      d.type = id.type;
      snprintf(d.name, sizeof(d.name), "Телефон %d", i + 1);
      rt[i] = {}; rt[i].conn = 0xFFFF;
      devLevel[i] = 0; saveLevels();
      saveDevs();
      pairUntil = 0; newPin(); fresh = true;
      logEv("Добавлено: %s (%s)", d.name, addrStr(d.addr).c_str());
      if (isRpa(id)) logEv("Внимание: телефон не сообщил постоянный адрес");
    } else {
      logEv("Чужое устройство %s отклонено", addrStr(id.val).c_str());
      removeBond(id.val);
      pServer->disconnect(s->handle);
      return;
    }
  }
  s->authed = true; s->dev = i;
  DevRt& r = rt[i];
  if (fresh || now < (uint32_t)graceSec * 1000UL) r.opened = true;
  else if (!(r.everSeen && (now - r.lastDisc) < (uint32_t)rearmSec * 1000UL)) r.opened = false;
  // просим телефон присылать пакеты каждые 20–30 мс (больше реальных измерений сигнала)
  // min/max в единицах 1,25 мс, таймаут в единицах 10 мс. Телефон может не согласиться.
  pServer->updateConnParams(s->handle, 16, 24, 0, 400);
  r.everSeen = true; r.present = true; r.conn = s->handle; r.rssi = -127; r.nearMs = now; r.hn = 0; r.hi = 0; r.aboveSince = 0;
  logEv("%s: подключился", devs[i].name);
}

void checkPending() {
  for (auto& s : slots) {
    if (!s.used || !s.pending) continue;
    uint32_t waited = millis() - s.authAt;
    if (waited < 1500) continue;
    ble_gap_conn_desc d;
    if (ble_gap_conn_find(s.handle, &d) != 0) { s.pending = false; continue; }
    if (isRpa(d.peer_id_addr) && waited < 6000) continue;   // ждём постоянный адрес
    s.pending = false;
    processAuth(&s, d.peer_id_addr);
  }
}

void deleteDev(int i) {
  if (rt[i].present) pServer->disconnect(rt[i].conn);
  removeBond(devs[i].addr);
  logEv("Удалено: %s", devs[i].name);
  for (auto& s : slots) if (s.used) { if (s.dev == i) s.dev = -1; else if (s.dev > i) s.dev--; }
  for (int k = i; k < devCount - 1; k++) { devs[k] = devs[k + 1]; rt[k] = rt[k + 1]; devLevel[k] = devLevel[k + 1]; }
  devLevel[devCount - 1] = 0; saveLevels();
  devCount--;
  rt[devCount] = {}; rt[devCount].conn = 0xFFFF;
  saveDevs();
}

// медиана последних измерений: одиночные скачки (например -110 рядом с ESP) не влияют
int8_t medianRssi(const DevRt& r) {
  int8_t t[RSSI_WIN];
  for (int k = 0; k < r.hn; k++) t[k] = r.hist[k];
  for (int a = 1; a < r.hn; a++) { int8_t x = t[a]; int b = a - 1; while (b >= 0 && t[b] > x) { t[b + 1] = t[b]; b--; } t[b + 1] = x; }
  return t[r.hn / 2];
}

void pollPresence() {
  static uint32_t last = 0;
  if (millis() - last < 100) return;   // 10 опросов в секунду
  last = millis();
  if (wifiOn) return;   // пока Wi-Fi включён, сигнал недостоверен — не измеряем и не открываем
  for (int i = 0; i < devCount; i++) {
    DevRt& r = rt[i];
    if (!r.present) continue;
    int8_t v = 0;
    if (ble_gap_conn_rssi(r.conn, &v) == 0 && v != 127 && v > -127) {
      r.raw = v;
      r.hist[r.hi] = v; r.hi = (r.hi + 1) % RSSI_WIN;
      if (r.hn < RSSI_WIN) r.hn++;
    }
    if (r.hn < 4) continue;           // мало данных
    r.rssi = medianRssi(r);

    int L = levelOf(i);

    // Ушёл: сигнал слабее уровня "у двери" минус запас, дольше rearmSec.
    // Только после этого разрешается следующее открытие.
    if (r.rssi >= L - awayHyst) r.nearMs = millis();
    else if (r.opened && millis() - r.nearMs >= (uint32_t)rearmSec * 1000UL) {
      r.opened = false;
      logEv("%s: ушёл (RSSI %d), следующее приближение откроет дверь", devs[i].name, r.rssi);
    }

    // Открыть: шёл издалека (opened == false) и пересёк уровень "у двери".
    // Если уже открыто — сильнее (проходите рядом) или слабее (уходите) не открывает.
    if (r.opened || r.rssi < L) { r.aboveSince = 0; continue; }
    if (!r.aboveSince) r.aboveSince = millis() | 1;
    if (millis() - r.aboveSince < confirmMs) continue;
    r.aboveSince = 0;
    r.opened = true;
    if (isBlocked(i)) { logEv("%s заблокирован — не открываю", devs[i].name); continue; }
    logEv("%s: приблизился, сигнал %d дБм пересёк уровень %d", devs[i].name, r.rssi, L);
    openDoor(devs[i].name);
  }
}

void checkSlots() {
  uint32_t lim = pairingActive() ? PAIR_WINDOW_MS : AUTH_TIMEOUT_MS;
  for (auto& s : slots)
    if (s.used && !s.authed && !s.pending && millis() - s.since > lim) { s.since = millis(); pServer->disconnect(s.handle); }
}

// ---------------------- сервисная веб-страница (только обновление прошивки) ----------------------
static const char PAGE[] = R"rawliteral(<!DOCTYPE html><html lang="ru"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>Замок — сервис</title>
<style>body{font-family:system-ui,sans-serif;max-width:480px;margin:auto;padding:14px;background:#f2f3f5;color:#222}
button{padding:10px 14px;border:0;border-radius:8px;background:#1e6fd9;color:#fff;margin:8px 8px 0 0;font-size:15px}</style></head><body>
<h3>🔒 Сервисный режим</h3>
<p>Управление замком — через Bluetooth. Здесь только обновление прошивки.</p>
<p><b>Версия прошивки: )rawliteral" FW_VERSION " " __DATE__ " " __TIME__ R"rawliteral(</b><br>После обновления откройте эту страницу снова: версия (время сборки) должна измениться.</p>
<input type="file" id="fw" accept=".bin"><br><button onclick="upd()">Загрузить .bin</button>
<button style="background:#e38b12" onclick="fetch('/api/reboot',{method:'POST'}).then(()=>alert('Перезагрузка'))">Перезагрузить</button>
<div id="prog"></div>
<script>
function upd(){const f=document.getElementById('fw').files[0],p=document.getElementById('prog');if(!f)return alert('Выберите файл .bin');
 const x=new XMLHttpRequest();x.open('POST','/update');
 let full=false;x.upload.onprogress=e=>{const q=Math.round(e.loaded*100/e.total);full=q>=100;p.textContent='Загрузка '+q+'%'};
 x.onload=()=>{p.textContent=x.responseText=='OK'?'Готово, перезагрузка…':x.responseText=='NOOTA'?'Эта схема разделов не поддерживает обновление по Wi-Fi. Один раз залейте скетч по USB, выбрав Tools → Partition Scheme → Minimal SPIFFS (with OTA).':'Ошибка обновления'};
 x.onerror=()=>{p.textContent=full?'Связь оборвалась после загрузки — возможно, замок уже перезагружается. Подождите 30 секунд и проверьте версию прошивки на странице управления.':'Ошибка связи во время загрузки'};
 const fd=new FormData();fd.append('fw',f);x.send(fd)}
</script></body></html>)rawliteral";

// Проверка: лежит ли выполняемый код в одном из app-разделов таблицы разделов.
// Если нет, Update.begin() внутри ESP-IDF вызывает abort() без всякого сообщения.
bool runningPartitionOk() {
  size_t phys = spi_flash_cache2phys((const void*)runningPartitionOk);
  if (phys == SPI_FLASH_CACHE2PHYS_FAIL) return false;
  esp_partition_iterator_t it = esp_partition_find(ESP_PARTITION_TYPE_APP, ESP_PARTITION_SUBTYPE_ANY, NULL);
  while (it) {
    const esp_partition_t* p = esp_partition_get(it);
    if (phys >= p->address && phys < p->address + p->size) { esp_partition_iterator_release(it); return true; }
    it = esp_partition_next(it);
  }
  return false;
}

// Сколько OTA-разделов приложения в таблице. Для обновления по Wi-Fi нужно минимум 2:
// новая прошивка пишется в тот раздел, из которого плата сейчас НЕ работает.
int otaSlots() {
  int n = 0;
  esp_partition_iterator_t it = esp_partition_find(ESP_PARTITION_TYPE_APP, ESP_PARTITION_SUBTYPE_ANY, NULL);
  while (it) {
    const esp_partition_t* p = esp_partition_get(it);
    if (p->subtype >= ESP_PARTITION_SUBTYPE_APP_OTA_MIN && p->subtype < ESP_PARTITION_SUBTYPE_APP_OTA_MAX) n++;
    it = esp_partition_next(it);
  }
  return n;
}

void printPartitions() {
  Serial.printf("Код выполняется по адресу flash 0x%X\n", (unsigned)spi_flash_cache2phys((const void*)printPartitions));
  esp_partition_iterator_t it = esp_partition_find(ESP_PARTITION_TYPE_ANY, ESP_PARTITION_SUBTYPE_ANY, NULL);
  while (it) {
    const esp_partition_t* p = esp_partition_get(it);
    Serial.printf("Раздел %-10s тип %d/%d адрес 0x%06X размер 0x%06X\n", p->label, (int)p->type, (int)p->subtype, (unsigned)p->address, (unsigned)p->size);
    it = esp_partition_next(it);
  }
}

bool auth() {
  lastActivity = millis();
  if (!server.authenticate(cfg.webUser.c_str(), cfg.webPass.c_str())) { server.requestAuthentication(); return false; }
  return true;
}

// ---------------------- Wi-Fi вкл/выкл ----------------------
// Wi-Fi нужен только для обновления прошивки. Пока он включён, автооткрытие приостановлено
// (радио одно на Wi-Fi и Bluetooth, замеры сигнала в это время недостоверны).
void enableWifi(const char* why) {
  lastActivity = millis();
  wifiLimit = wifiBootWin ? 10000UL : (uint32_t)woffSec * 1000UL;
  wifiBootWin = false;
  if (wifiOn) return;
  WiFi.mode(WIFI_AP);
  WiFi.softAP(cfg.apSsid.c_str(), cfg.apPass.c_str(), 6, 0, 3);
  if (MDNS.begin(MDNS_NAME)) MDNS.addService("http", "tcp", 80);
  server.begin();
  wifiOn = true;
  logEv("Wi-Fi включён (%s)", why);
}

void disableWifi() {
  if (!wifiOn) return;
  logEv("Wi-Fi выключен");
  MDNS.end();
  server.stop();
  WiFi.softAPdisconnect(true);
  WiFi.mode(WIFI_OFF);
  wifiOn = false;
  for (int i = 0; i < MAX_DEVICES; i++) { rt[i].nearMs = millis(); rt[i].aboveSince = 0; rt[i].hn = 0; rt[i].hi = 0; }
}

void checkWifiIdle() {
  static uint32_t last = 0;
  if (millis() - last < 1000) return;
  last = millis();
  if (!wifiOn) return;
  if (WiFi.softAPgetStationNum() > 0) {
    lastActivity = millis();
    // кто-то подключился в первые 10 с — дальше работаем по обычному таймауту
    if (wifiLimit && wifiLimit < 30000UL) wifiLimit = (uint32_t)woffSec * 1000UL;
  }
  if (wifiLimit && millis() - lastActivity > wifiLimit) disableWifi();
}

void setupWeb() {
  server.on("/", HTTP_GET, []() { if (!auth()) return; server.send(200, "text/html; charset=utf-8", PAGE); });
  server.on("/api/reboot", HTTP_POST, []() {
    if (!auth()) return;
    logEv("Перезагрузка из сервисной страницы");
    rebootAt = millis() + 800;
    server.send(200, "application/json", "{\"ok\":true}");
  });
  // обновление прошивки через браузер
  server.on("/update", HTTP_POST, []() {
    if (!auth()) return;
    bool good = otaAuthOk && !Update.hasError();
    server.sendHeader("Connection", "close");
    server.send(200, "text/plain", good ? "OK" : (otaNoSlots ? "NOOTA" : "FAIL"));
    if (!otaNoSlots) rebootAt = millis() + (good ? 1000 : 2500);   // при ошибке тоже перезапуск: вернёт Bluetooth
  }, []() {
    HTTPUpload& up = server.upload();
    if (up.status == UPLOAD_FILE_START) {
      otaAuthOk = server.authenticate(cfg.webUser.c_str(), cfg.webPass.c_str());
      if (!otaAuthOk) return;
      otaNoSlots = false;
      if (!runningPartitionOk() || otaSlots() < 2) {
        otaAuthOk = false;   // ответ будет NOOTA, плата не упадёт
        otaNoSlots = true;
        logEv("OTA невозможно: нет второго раздела app");
        Serial.println("OTA отменено: в схеме разделов меньше двух app-разделов. Выберите Minimal SPIFFS (с OTA) и залейте скетч по USB.");
        return;
      }
      logEv("Обновление прошивки: начало");
      // Bluetooth полностью останавливаем до конца обновления (освобождает память и не мешает
      // стиранию/записи флеша). После обновления или ошибки плата перезагрузится и вернёт его.
      otaBusy = true;
      Serial.printf("OTA: память до остановки BLE: свободно %u, макс. блок %u\n", (unsigned)ESP.getFreeHeap(), (unsigned)ESP.getMaxAllocHeap());
      NimBLEDevice::deinit(true);
      respStr = String();
      WiFi.setTxPower(WIFI_POWER_11dBm);
      Serial.printf("OTA: память после остановки BLE: свободно %u, макс. блок %u\n", (unsigned)ESP.getFreeHeap(), (unsigned)ESP.getMaxAllocHeap());
      if (!Update.begin(UPDATE_SIZE_UNKNOWN)) Update.printError(Serial);
    } else if (up.status == UPLOAD_FILE_WRITE) {
      lastActivity = millis();
      if (otaAuthOk && Update.write(up.buf, up.currentSize) != up.currentSize) Update.printError(Serial);
    } else if (up.status == UPLOAD_FILE_END) {
      if (otaAuthOk) {
        if (Update.end(true)) logEv("Прошивка загружена (%u байт)", (unsigned)up.totalSize);
        else { Update.printError(Serial); logEv("Ошибка обновления"); }
      }
    } else if (up.status == UPLOAD_FILE_ABORTED) {
      if (otaAuthOk) { Update.abort(); logEv("Обновление прервано (обрыв связи)"); rebootAt = millis() + 1500; }
    }
  });
  server.onNotFound([]() { server.send(404, "text/plain", "404"); });
}

// ---------------------- Bluetooth-управление (GATT) ----------------------
// Два характеристики, оба только для сопряжённых и зашифрованных соединений:
//   CMD (запись) — текстовые команды; RSP (чтение) — ответ кусками по CHUNK байт.
// Первый байт ответа: 'M' — есть ещё кусок, 'L' — последний. Следующий кусок: записать в CMD "g<N>".
#define SVC_UUID "6c5f0001-8d4e-4b1a-9a3f-2f7b5c1d0a01"
#define CMD_UUID "6c5f0002-8d4e-4b1a-9a3f-2f7b5c1d0a01"
#define RSP_UUID "6c5f0003-8d4e-4b1a-9a3f-2f7b5c1d0a01"
#define CHUNK 240

QueueHandle_t cmdQueue;
NimBLECharacteristic* pRsp = nullptr;

bool openPairing(const char* why) {
  if (devCount >= MAX_DEVICES) { logEv("Список полон (%d)", MAX_DEVICES); return false; }
  newPin();
  pairUntil = millis() + PAIR_WINDOW_MS;
  if (pairUntil == 0) pairUntil = 1;
  logEv("Режим добавления включён (%s)", why);
  return true;
}

String buildStatus() {
  bool pa = pairingActive();
  char pb[8]; snprintf(pb, sizeof(pb), "%06lu", (unsigned long)storedPin);
  String j; j.reserve(3000);
  j = "{\"ver\":\"" FW_VERSION " " __DATE__ " " __TIME__ "\",\"ble\":\""; j += jsEsc(cfg.bleName.c_str());
  j += "\",\"pin\":\""; j += pb;
  j += "\",\"pairing\":"; j += pa ? "true" : "false";
  j += ",\"pairLeft\":"; j += pa ? (unsigned long)((pairUntil - millis()) / 1000) : 0UL;
  j += ",\"maxDev\":"; j += (int)MAX_DEVICES;
  j += ",\"rssiThr\":"; j += (int)rssiThr;
  j += ",\"rearm\":"; j += (int)rearmSec;
  j += ",\"pulse\":"; j += (int)pulseMs;
  j += ",\"tx\":"; j += (int)txLevel;
  j += ",\"grace\":"; j += (int)graceSec;
  j += ",\"hyst\":"; j += (int)awayHyst;
  j += ",\"conf\":"; j += (int)confirmMs;
  j += ",\"woff\":"; j += (int)woffSec;
  j += ",\"rlow\":"; j += cfg.relayLow ? "true" : "false";
  j += ",\"tv\":"; j += timeValid ? "true" : "false";
  j += ",\"ota\":"; j += otaSlots();
  j += ",\"wifi\":"; j += wifiOn ? "true" : "false";
  j += ",\"ap\":\""; j += jsEsc(cfg.apSsid.c_str());
  j += "\",\"app\":\""; j += jsEsc(cfg.apPass.c_str());
  j += "\",\"wu\":\""; j += jsEsc(cfg.webUser.c_str());
  j += "\",\"wp\":\""; j += jsEsc(cfg.webPass.c_str());
  j += "\",\"m\":\""; j += jsEsc(lastMsg.c_str());
  j += "\",\"devices\":[";
  for (int i = 0; i < devCount; i++) {
    if (i) j += ',';
    j += "{\"addr\":\""; j += addrStr(devs[i].addr);
    j += "\",\"name\":\""; j += jsEsc(devs[i].name);
    j += "\",\"blocked\":"; j += isBlocked(i) ? "true" : "false";
    j += ",\"until\":"; j += (unsigned long)devs[i].blockUntil;
    j += ",\"connected\":"; j += rt[i].present ? "true" : "false";
    j += ",\"rssi\":"; j += (int)rt[i].rssi;
    j += ",\"level\":"; j += (int)levelOf(i);
    j += ",\"cal\":"; j += devLevel[i] ? "true" : "false";
    j += ",\"armed\":"; j += (rt[i].present && !rt[i].opened) ? "true" : "false";
    j += ",\"raw\":"; j += (int)(rt[i].hn ? rt[i].raw : -127);
    j += "}";
  }
  j += "]}";
  return j;
}

String buildLog() {
  String j = "[";
  for (int k = 0; k < logCount; k++) {
    int idx = (logHead + LOG_SIZE - 1 - k) % LOG_SIZE;
    if (k) j += ',';
    j += "{\"ago\":"; j += (unsigned long)((millis() - logs[idx].ms) / 1000);
    j += ",\"t\":\""; j += jsEsc(logs[idx].text); j += "\"}";
  }
  j += "]";
  return j;
}

void setChunk(int n) {
  size_t off = (size_t)n * CHUNK;
  bool last = off + CHUNK >= respStr.length();
  String out = String(last ? 'L' : 'M');
  if (off < respStr.length()) out += respStr.substring(off, off + CHUNK);
  pRsp->setValue((const uint8_t*)out.c_str(), out.length());
}

class CmdCb : public NimBLECharacteristicCallbacks {
  void onWrite(NimBLECharacteristic* c, ble_gap_conn_desc* d) override {
    std::string v = c->getValue();
    Slot* s = getSlot(d->conn_handle, false);
    // команды принимаются только от телефона, которого замок уже признал и который не заблокирован
    if (!(s && s->authed && s->dev >= 0 && !isBlocked(s->dev))) {
      respStr = "{\"err\":\"not ready\"}"; setChunk(0); return;
    }
    if (v == "s") { respStr = buildStatus(); lastMsg = ""; setChunk(0); return; }
    if (v == "l") { respStr = buildLog(); setChunk(0); return; }
    if (v.size() > 1 && v[0] == 'g') { setChunk(atoi(v.c_str() + 1)); return; }
    Cmd cm; cm.conn = d->conn_handle;
    strncpy(cm.text, v.c_str(), sizeof(cm.text) - 1); cm.text[sizeof(cm.text) - 1] = 0;
    xQueueSend(cmdQueue, &cm, 0);
  }
};
CmdCb cmdCb;

bool isDigitsOnly(const String& s) {
  if (!s.length()) return false;
  for (size_t i = 0; i < s.length(); i++) if (s[i] < '0' || s[i] > '9') return false;
  return true;
}

void cmdSet(const String& a) {
  int sp = a.indexOf(' ');
  if (sp < 0) { lastMsg = "Неверная команда"; return; }
  String k = a.substring(0, sp), v = a.substring(sp + 1); v.trim();
  long n = v.toInt();
  bool good = true, st = false;
  if      (k == "rssi")  { if (n >= -110 && n <= -25) { rssiThr = (int8_t)n; st = true; } else good = false; }
  else if (k == "hyst")  { if (n >= 2 && n <= 30)     { awayHyst = (uint8_t)n; st = true; } else good = false; }
  else if (k == "conf")  { if (n >= 0 && n <= 10000)  { confirmMs = (uint16_t)n; st = true; } else good = false; }
  else if (k == "rearm") { if (n >= 0 && n <= 3600)   { rearmSec = (uint16_t)n; st = true; } else good = false; }
  else if (k == "grace") { if (n >= 0 && n <= 600)    { graceSec = (uint16_t)n; st = true; } else good = false; }
  else if (k == "pulse") { if (n >= 200 && n <= 10000){ pulseMs = (uint16_t)n; st = true; } else good = false; }
  else if (k == "tx")    { if (n >= 0 && n <= 7)      { txLevel = (uint8_t)n; applyTxPower(); st = true; } else good = false; }
  else if (k == "woff")  { if (n >= 30 && n <= 3600)  { woffSec = (uint16_t)n; prefs.putUShort("woff", woffSec); } else good = false; }
  else if (k == "rlow")  { cfg.relayLow = (n == 1); prefs.putBool("rlow", cfg.relayLow); initRelayPin(); }
  else if (k == "pin")   { if (v.length() == 6 && isDigitsOnly(v)) { storedPin = (uint32_t)n; prefs.putUInt("pin", storedPin); newPin(); lastMsg = "Новый PIN действует для новых сопряжений"; } else good = false; }
  else if (k == "ble")   { if (v.length() >= 1 && v.length() <= 20) { cfg.bleName = v; prefs.putString("ble", v); lastMsg = "Имя изменится после перезагрузки"; } else good = false; }
  else if (k == "apssid"){ if (v.length() >= 1 && v.length() <= 32) { cfg.apSsid = v; prefs.putString("ap_ssid", v); } else good = false; }
  else if (k == "appass"){ if (v.length() >= 8 && v.length() <= 63) { cfg.apPass = v; prefs.putString("ap_pass", v); } else good = false; }
  else if (k == "webpass"){ if (v.length() >= 4 && v.length() <= 63) { cfg.webPass = v; prefs.putString("w_pass", v); } else good = false; }
  else good = false;
  if (!good) lastMsg = "Неверное значение";
  else if (st) { saveSettings(); logEv("Настройка изменена: %s", k.c_str()); }
}

void runCmd(const Cmd& cm) {
  String c(cm.text); c.trim();
  int sp = c.indexOf(' ');
  String op = sp < 0 ? c : c.substring(0, sp);
  String a  = sp < 0 ? String("") : c.substring(sp + 1);
  lastMsg = "";
  Slot* s = getSlot(cm.conn, false);
  const char* who = (s && s->dev >= 0) ? devs[s->dev].name : "Bluetooth";

  if (op == "open")     { openDoor(who); return; }
  if (op == "pair")     { if (!openPairing("Bluetooth")) lastMsg = "Список устройств полон"; return; }
  if (op == "pairstop") { pairUntil = 0; newPin(); return; }
  if (op == "wifi")     { enableWifi("Bluetooth"); return; }
  if (op == "wifioff")  { disableWifi(); return; }
  if (op == "reboot")   { logEv("Перезагрузка по Bluetooth"); rebootAt = millis() + 800; return; }
  if (op == "set")      { cmdSet(a); return; }
  if (op == "time") {
    long t = a.toInt();
    if (t > 1700000000L) { struct timeval tv = { (time_t)t, 0 }; settimeofday(&tv, nullptr); timeValid = true; }
    return;
  }

  // команды с адресом телефона: "<команда> aa:bb:cc:dd:ee:ff [параметр]"
  uint8_t ab[6];
  int i = (a.length() >= 17 && parseAddr(a.substring(0, 17), ab)) ? findDev(ab) : -1;
  String rest = a.length() > 18 ? a.substring(18) : String("");
  rest.trim();
  if (i < 0) { lastMsg = "Телефон не найден"; return; }

  if (op == "cal") {
    if (wifiOn) { lastMsg = "Сначала выключите Wi-Fi: при нём сигнал недостоверен"; return; }
    if (!rt[i].present || rt[i].hn < 3 || rt[i].rssi <= -110) { lastMsg = "Сигнал ещё не измерен, подождите пару секунд"; return; }
    int v = rt[i].rssi - 3;
    if (v < -110) v = -110;
    devLevel[i] = (int8_t)v; saveLevels();
    rt[i].nearMs = millis();
    logEv("%s: уровень у двери записан: %d дБм (сигнал %d)", devs[i].name, v, rt[i].rssi);
    return;
  }
  if (op == "lvl") {
    long n = rest.toInt();
    if (rest.length() == 0 || n < -110 || n > -25) { lastMsg = "Уровень должен быть от -110 до -25 дБм"; return; }
    devLevel[i] = (int8_t)n; saveLevels();
    rt[i].nearMs = millis();
    logEv("%s: уровень у двери задан вручную: %ld дБм", devs[i].name, n);
    return;
  }
  if (op == "calreset") { devLevel[i] = 0; saveLevels(); logEv("%s: уровень у двери сброшен", devs[i].name); return; }
  if (op == "ren") {
    if (!rest.length()) { lastMsg = "Пустое имя"; return; }
    safeCopy(devs[i].name, sizeof(devs[i].name), rest.c_str()); saveDevs(); return;
  }
  if (op == "blk") {
    String hs = rest; hs.replace(',', '.');
    float h = hs.toFloat();
    if (hs == "0") { devs[i].blocked = 1; devs[i].blockUntil = 0; logEv("%s заблокирован бессрочно", devs[i].name); }
    else {
      if (h <= 0 || !timeValid) { lastMsg = "Неверное время или часы не синхронизированы"; return; }
      devs[i].blocked = 0;
      devs[i].blockUntil = (uint32_t)time(nullptr) + (uint32_t)(h * 3600.0f);
      logEv("%s заблокирован на %.1f ч", devs[i].name, h);
    }
    saveDevs(); return;
  }
  if (op == "unb") { devs[i].blocked = 0; devs[i].blockUntil = 0; logEv("%s разблокирован", devs[i].name); saveDevs(); return; }
  if (op == "del") { deleteDev(i); return; }
  lastMsg = "Неизвестная команда";
}

// ---------------------- setup / loop ----------------------
void setup() {
  Serial.begin(115200);
  prefs.begin("lock", false);
  loadCfg();
  initRelayPin();
  pinMode(LED_PIN, OUTPUT);
  pinMode(BUTTON_PIN, INPUT_PULLUP);
  pinMode(BOOT_BTN_PIN, INPUT_PULLUP);

  evQueue = xQueueCreate(16, sizeof(BleEvent));
  cmdQueue = xQueueCreate(8, sizeof(Cmd));
  loadAll();

  setupWeb();
  wifiBootWin = true;
  enableWifi("запуск");

  NimBLEDevice::init(std::string(cfg.bleName.c_str()));
  applyTxPower();
  NimBLEDevice::setSecurityAuth(true, true, true);
  NimBLEDevice::setSecurityIOCap(BLE_HS_IO_DISPLAY_ONLY);
  // Обмен ключами идентификации (IRK): ESP32 получает от телефона ключ, по которому
  // узнаёт его, даже когда телефон меняет случайный MAC (после выкл/вкл Bluetooth).
  // Собственный адрес ESP32 остаётся постоянным (публичным).
  NimBLEDevice::setSecurityInitKey(BLE_SM_PAIR_KEY_DIST_ENC | BLE_SM_PAIR_KEY_DIST_ID);
  NimBLEDevice::setSecurityRespKey(BLE_SM_PAIR_KEY_DIST_ENC | BLE_SM_PAIR_KEY_DIST_ID);
  newPin();
  cleanupBonds();

  pServer = NimBLEDevice::createServer();
  pServer->setCallbacks(new SrvCb());

  NimBLEHIDDevice* hid = new NimBLEHIDDevice(pServer);
  hid->manufacturer()->setValue(std::string("DIY"));
  hid->pnp(0x02, 0x303A, 0x4001, 0x0100);
  hid->hidInfo(0x00, 0x01);
  hid->reportMap((uint8_t*)HID_MAP, sizeof(HID_MAP));
  hid->inputReport(1);
  hid->setBatteryLevel(100);
  hid->startServices();

  NimBLEService* svc = pServer->createService(SVC_UUID);
  NimBLECharacteristic* pCmd = svc->createCharacteristic(CMD_UUID,
      NIMBLE_PROPERTY::WRITE | NIMBLE_PROPERTY::WRITE_ENC | NIMBLE_PROPERTY::WRITE_AUTHEN);
  pRsp = svc->createCharacteristic(RSP_UUID,
      NIMBLE_PROPERTY::READ | NIMBLE_PROPERTY::READ_ENC | NIMBLE_PROPERTY::READ_AUTHEN);
  pCmd->setCallbacks(&cmdCb);
  pRsp->setValue("L{}");
  svc->start();

  NimBLEAdvertising* adv = NimBLEDevice::getAdvertising();
  adv->setAppearance(0x03C0);
  adv->addServiceUUID(hid->hidService()->getUUID());
  adv->setScanResponse(true);
  adv->start();

  const char* why = "другая";
  switch (esp_reset_reason()) {
    case ESP_RST_POWERON:  why = "включение питания"; break;
    case ESP_RST_BROWNOUT: why = "ПРОСАДКА ПИТАНИЯ (слабый БП/DC-DC)"; break;
    case ESP_RST_PANIC:    why = "ошибка программы"; break;
    case ESP_RST_SW:       why = "программная перезагрузка"; break;
    case ESP_RST_EXT:      why = "кнопка EN"; break;
    case ESP_RST_INT_WDT:
    case ESP_RST_TASK_WDT:
    case ESP_RST_WDT:      why = "сторожевой таймер"; break;
    default: break;
  }
  logEv("Запуск v" FW_VERSION " (" __DATE__ " " __TIME__ "), причина: %s. Wi-Fi: %s", why, cfg.apSsid.c_str());
  logEv("OTA-разделов: %d (нужно 2). Раздел: %s", otaSlots(), runningPartitionOk() ? "найден" : "НЕ НАЙДЕН");
  printPartitions();
}

void loop() {
  if (otaBusy) {   // идёт обновление: Bluetooth остановлен, работаем только с веб-сервером
    if (wifiOn) server.handleClient();
    if (rebootAt && (int32_t)(millis() - rebootAt) >= 0) ESP.restart();
    if (!rebootAt && millis() - lastActivity > 90000UL) ESP.restart();   // страховка от зависания
    delay(2);
    return;
  }
  BleEvent e;
  while (xQueueReceive(evQueue, &e, 0) == pdTRUE) handleEvent(e);
  Cmd cm;
  while (xQueueReceive(cmdQueue, &cm, 0) == pdTRUE) runCmd(cm);

  if (wifiOn) server.handleClient();
  if (otaBusy) { delay(2); return; }   // обновление началось внутри handleClient — Bluetooth уже остановлен
  checkWifiIdle();
  checkPending();
  pollPresence();
  checkSlots();

  if (relayActive && millis() - relayStart >= pulseMs) { relayActive = false; relayOut(false); }
  if (pairUntil && !pairingActive()) { pairUntil = 0; newPin(); logEv("Режим добавления завершён"); }
  if (rebootAt && (int32_t)(millis() - rebootAt) >= 0) ESP.restart();

  // кнопка выхода
  // срабатывает только если кнопка стабильно нажата 100 мс (защита от помех на проводе)
  static bool btnState = HIGH, btnRaw = HIGH; static uint32_t tBtn = 0;
  bool b = digitalRead(BUTTON_PIN);
  if (b != btnRaw) { btnRaw = b; tBtn = millis(); }
  if (btnRaw != btnState && millis() - tBtn > 100) {
    btnState = btnRaw;
    if (btnState == LOW && millis() > 3000) openDoor("кнопка выхода");
  }
  // удержание кнопки выхода 5 с — включить Wi-Fi
  static bool btnWifiDone = false;
  if (btnState == LOW && !btnWifiDone && millis() - tBtn > WIFI_BTN_HOLD_MS) { btnWifiDone = true; enableWifi("кнопка выхода"); }
  if (btnState == HIGH) btnWifiDone = false;

  // кнопка BOOT: удержание 10 с — сброс сети и паролей
  // короткое нажатие BOOT — окно добавления телефона; 2–7 с — включить Wi-Fi
  static uint32_t bootPressed = 0;
  if (digitalRead(BOOT_BTN_PIN) == LOW) {
    if (!bootPressed) bootPressed = millis() | 1;
    else if (millis() - bootPressed > NET_RESET_HOLD_MS && !rebootAt) resetNetCfg();
  } else {
    if (bootPressed) {
      uint32_t held = millis() - bootPressed;
      if (held > 50 && held < 2000) openPairing("кнопка BOOT");
      else if (held >= 2000 && held < 7000) enableWifi("кнопка BOOT");
    }
    bootPressed = 0;
  }

  // светодиод
  if (bootPressed && millis() - bootPressed > 7000) digitalWrite(LED_PIN, (millis() / 80) % 2);
  else if (relayActive) digitalWrite(LED_PIN, HIGH);
  else if (pairingActive()) digitalWrite(LED_PIN, (millis() / 250) % 2);
  else digitalWrite(LED_PIN, LOW);

  delay(2);
}
