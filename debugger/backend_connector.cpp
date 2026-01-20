#include "backend_connector.h"
#include <QDebug>
#include <QJsonArray>
#include <QJsonDocument>
#include <QJsonObject>

BackendConnector::BackendConnector(QObject *parent)
    : QObject(parent), m_socket(new QTcpSocket(this)), m_connected(false),
      m_paused(false) {
  connect(m_socket, &QTcpSocket::readyRead, this,
          &BackendConnector::onReadyRead);
  connect(m_socket, &QTcpSocket::stateChanged, this,
          &BackendConnector::onSocketStateChanged);
  connect(m_socket, &QTcpSocket::errorOccurred, this,
          &BackendConnector::onErrorOccurred);
}

bool BackendConnector::connected() const { return m_connected; }

bool BackendConnector::paused() const { return m_paused; }

QStringList BackendConnector::stack() const { return m_stack; }

QString BackendConnector::bindings() const { return m_bindings; }

void BackendConnector::connectToDebugger(int port) {
  if (m_connected)
    return;

  qDebug() << "Connecting to debugger on port" << port;
  m_socket->connectToHost("127.0.0.1", port);
}

void BackendConnector::disconnectFromDebugger() {
  m_socket->disconnectFromHost();
}

void BackendConnector::pause() { sendCommand("pause"); }

void BackendConnector::resume() { sendCommand("resume"); }

void BackendConnector::stepInto() { sendCommand("step_into"); }

void BackendConnector::stepOver() { sendCommand("step_over"); }

void BackendConnector::stepOut() { sendCommand("step_out"); }

void BackendConnector::refresh() {
  sendCommand("get_stack");
  // Also get bindings
  sendCommand("get_bindings");
}

void BackendConnector::onSocketStateChanged(
    QAbstractSocket::SocketState socketState) {
  bool wasConnected = m_connected;
  m_connected = (socketState == QAbstractSocket::ConnectedState);

  if (wasConnected != m_connected) {
    emit connectedChanged(m_connected);
    if (m_connected) {
      qDebug() << "Connected!";
      // Initial refresh
      refresh();
    } else {
      qDebug() << "Disconnected.";
    }
  }
}

void BackendConnector::onErrorOccurred(
    QAbstractSocket::SocketError socketError) {
  qWarning() << "Socket Error:" << m_socket->errorString();
}

void BackendConnector::onReadyRead() {
  while (m_socket->canReadLine()) {
    QByteArray line = m_socket->readLine();
    processMessage(line);
  }
}

void BackendConnector::processMessage(const QByteArray &message) {
  QJsonParseError parseError;
  QJsonDocument doc = QJsonDocument::fromJson(message, &parseError);

  if (parseError.error != QJsonParseError::NoError) {
    qWarning() << "JSON Parse Error:" << parseError.errorString() << message;
    return;
  }

  if (doc.isObject()) {
    QJsonObject obj = doc.object();

    // Handle specialized responses (Stack, Bindings)
    if (obj.contains("Stack")) {
      QJsonArray stackArray = obj["Stack"].toArray();
      QStringList newStack;
      for (const auto &val : stackArray) {
        // Nodes are u32, convert to string
        newStack.append(QString::number(val.toVariant().toUInt()));
      }
      if (m_stack != newStack) {
        m_stack = newStack;
        emit stackChanged(m_stack);
      }
    }

    if (obj.contains("Bindings")) {
      QString newBindings = obj["Bindings"].toString();
      if (m_bindings != newBindings) {
        m_bindings = newBindings;
        emit bindingsChanged(m_bindings);
      }
    }

    // TODO: Handle 'Paused' events if we add them to the implicit protocol
  }
}

void BackendConnector::sendCommand(const QString &cmd, int pid) {
  if (!m_connected)
    return;

  QJsonObject json;
  json["command"] = cmd;
  json["pid"] = pid;

  QJsonDocument doc(json);
  m_socket->write(doc.toJson(QJsonDocument::Compact) + "\n");
  m_socket->flush();
}
