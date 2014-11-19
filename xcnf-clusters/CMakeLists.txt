project(xcnf-clusters)
    include_directories(/usr/local/include/igraph)
cmake_minimum_required( VERSION 2.4.5 )
include_directories(/home/tero/include /home/tero/include/igraph)
link_directories(/home/tero/lib)    
mark_as_advanced(CMAKE_BACKWARDS_COMPATIBILITY)
set(FLAGS  "-Wall ")
if(CMAKE_BUILD_TYPE MATCHES "debug")
    set(CMAKE_CXX_FLAGS "-g -ggdb ${FLAGS}")
    set(DEBUG 1)
    add_definitions("-DDEBUG -DVERIFY")
    message("Debugging symbols")
else(CMAKE_BUILD_TYPE MATCHES "debug")
#   add_definitions("-DNDEBUG")
    message("No debugging symbols")
endif(CMAKE_BUILD_TYPE MATCHES "debug")

if(CMAKE_BUILD_TYPE MATCHES "profile")
    set(CMAKE_CXX_FLAGS "${FLAGS} -g -O2")
    message("Profiling build")
endif(CMAKE_BUILD_TYPE MATCHES "profile")
add_executable(xcnf-clusters xcnf-clusters.cpp)
    
target_link_libraries(xcnf-clusters boost_program_options)
add_executable(xcnf-junction-tree xcnf-junction-tree.cpp)
add_executable(xcnf-decompose xcnf-decompose.cpp)
add_executable(xcnf-decompose2 xcnf-decompose2.cpp)
add_executable(xcnf-combine xcnf-combine.cpp)

add_executable(xcnf-cut xcnf-cut.cpp)

    
target_link_libraries(xcnf-decompose boost_program_options igraph)
target_link_libraries(xcnf-decompose2 boost_program_options)


target_link_libraries(xcnf-cut boost_program_options igraph)

target_link_libraries(xcnf-junction-tree boost_program_options igraph)
