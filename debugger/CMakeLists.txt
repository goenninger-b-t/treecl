cmake_minimum_required(VERSION 3.16)

project(TreeCLDebugger VERSION 0.1 LANGUAGES CXX)

set(CMAKE_CXX_STANDARD 17)
set(CMAKE_CXX_STANDARD_REQUIRED ON)

find_package(Qt6 REQUIRED COMPONENTS Quick Core Network)

set(CMAKE_AUTOMOC ON)
set(CMAKE_AUTORCC ON)
set(CMAKE_AUTOUIC ON)

add_executable(treecl-debug
    main.cpp
    backend_connector.cpp
    backend_connector.h
    ui/qml_resources.qrc
)

target_link_libraries(treecl-debug
    PRIVATE Qt6::Quick Qt6::Core Qt6::Network
)
