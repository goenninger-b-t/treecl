#ifndef BACKEND_CONNECTOR_H
#define BACKEND_CONNECTOR_H

#include <QObject>
#include <QTcpSocket>
#include <QStringList>
#include <QVariantList>

class BackendConnector : public QObject
{
    Q_OBJECT
    Q_PROPERTY(bool connected READ connected NOTIFY connectedChanged)
    Q_PROPERTY(bool paused READ paused NOTIFY pausedChanged)
    Q_PROPERTY(QStringList stack READ stack NOTIFY stackChanged)
    Q_PROPERTY(QString bindings READ bindings NOTIFY bindingsChanged)

public:
    explicit BackendConnector(QObject *parent = nullptr);

    bool connected() const;
    bool paused() const;
    QStringList stack() const;
    QString bindings() const;

public slots:
    void connectToDebugger(int port);
    void disconnectFromDebugger();
    
    // Commands
    void pause();
    void resume();
    void stepInto();
    void stepOver();
    void stepOut();
    void refresh();

signals:
    void connectedChanged(bool connected);
    void pausedChanged(bool paused);
    void stackChanged(QStringList stack);
    void bindingsChanged(QString bindings);

private slots:
    void onReadyRead();
    void onSocketStateChanged(QAbstractSocket::SocketState socketState);
    void onErrorOccurred(QAbstractSocket::SocketError socketError);

private:
    void sendCommand(const QString &cmd, int pid = 1);
    void processMessage(const QByteArray &message);

    QTcpSocket *m_socket;
    bool m_connected;
    bool m_paused;
    QStringList m_stack;
    QString m_bindings;
};

#endif // BACKEND_CONNECTOR_H
