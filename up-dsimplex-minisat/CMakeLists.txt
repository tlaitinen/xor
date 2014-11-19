project(up-dsimplex-minisat)
cmake_minimum_required( VERSION 2.4.5 )
if(COMMAND cmake_policy)
cmake_policy(SET CMP0003 NEW)
endif(COMMAND cmake_policy)

set(CMAKE_BUILD_TYPE_SHARED_LIBS ON)
set(CMAKE_CXX_FLAGS_DEBUG "-Wall -g")    
include_directories(src)
file(GLOB libsrc src/*.cpp src/*.cc)
add_library(matrix ${libsrc})
#add_definitions("-DTRACK_DUPLICATES")
if(CMAKE_BUILD_TYPE MATCHES "debug")
add_definitions("-DDEBUG")
add_definitions("-DCHECK")
else(CMAKE_BUILD_TYPE MATCHES "debug")
    add_definitions("-DNDEBUG")

    message("No debugging symbols")
endif(CMAKE_BUILD_TYPE MATCHES "debug")
if(CMAKE_BUILD_TYPE MATCHES "profile")
    set(CMAKE_CXX_FLAGS "${FLAGS} -g -O3")
    message("Profiling build")
endif(CMAKE_BUILD_TYPE MATCHES "profile")

set(INST_DIR ${CMAKE_SOURCE_DIR}/dist)
set(INSTALL_OPTS LIBRARY DESTINATION ${INST_DIR}
                 RUNTIME DESTINATION ${INST_DIR})

add_subdirectory(minisat)


