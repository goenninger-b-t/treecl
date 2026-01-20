import QtQuick 2.15
import QtQuick.Controls 2.15
import QtQuick.Layouts 1.15

ApplicationWindow {
    visible: true
    width: 800
    height: 600
    title: "TreeCL Debugger"

    ColumnLayout {
        anchors.fill: parent
        spacing: 10
        anchors.margins: 10

        // Toolbar
        RowLayout {
            Layout.fillWidth: true
            
            Button {
                text: backend.connected ? "Disconnect" : "Connect"
                onClicked: backend.connect_to_debugger(9000)
            }

            Rectangle { width: 20; height: 1; color: "transparent" } // Spacer

            Button {
                text: "Resume"
                enabled: backend.connected
                onClicked: backend.resume()
            }
            
            Button {
                text: "Pause"
                enabled: backend.connected
                onClicked: backend.pause()
            }

            Button {
                text: "Step Into"
                enabled: backend.connected
                onClicked: backend.step_into()
            }

            Button {
                text: "Step Over"
                enabled: backend.connected
                onClicked: backend.step_over()
            }
            
            Button {
                text: "Step Out"
                enabled: backend.connected
                onClicked: backend.step_out()
            }

             Button {
                text: "Refresh Stack"
                enabled: backend.connected
                onClicked: backend.refresh()
            }
        }

        // Main Content
        SplitView {
            Layout.fillWidth: true
            Layout.fillHeight: true
            orientation: Qt.Horizontal

            // Source View (Placeholder)
            Rectangle {
                SplitView.preferredWidth: 500
                color: "#f0f0f0"
                border.color: "#ccc"
                
                Text {
                    anchors.centerIn: parent
                    text: "Source Code View (TODO)"
                }
            }
            
            // Sidebar (Stack & Locals)
            SplitView {
                SplitView.preferredWidth: 300
                orientation: Qt.Vertical
                
                // Call Stack
                Rectangle {
                    SplitView.preferredHeight: 300
                    color: "white"
                    border.color: "#ccc"
                    
                    ColumnLayout {
                        anchors.fill: parent
                        Text { 
                            text: "Call Stack" 
                            font.bold: true
                            Layout.margins: 5
                        }
                        
                        ListView {
                            Layout.fillWidth: true
                            Layout.fillHeight: true
                            model: backend.stack
                            delegate: ItemDelegate {
                                text: "Node " + modelData
                                width: parent.width
                            }
                        }
                    }
                }
                
                // Locals/Bindings
                Rectangle {
                    SplitView.fillHeight: true
                    color: "white"
                    border.color: "#ccc"
                    
                    ColumnLayout {
                        anchors.fill: parent
                        Text { 
                            text: "Variables"
                            font.bold: true
                            Layout.margins: 5
                        }
                        
                        TextArea {
                            Layout.fillWidth: true
                            Layout.fillHeight: true
                            readOnly: true
                            text: backend.bindings
                            font.family: "Courier New"
                        }
                    }
                }
            }
        }
        
        // Status Bar
        Rectangle {
            Layout.fillWidth: true
            height: 30
            color: "#e0e0e0"
            
            RowLayout {
                anchors.fill: parent
                anchors.margins: 5
                
                Text {
                    text: backend.connected ? "Connected" : "Disconnected"
                    color: backend.connected ? "green" : "red"
                }
                
                Text {
                    text: "| PID: 1"
                }
            }
        }
    }
}
