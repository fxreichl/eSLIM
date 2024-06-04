project(aiger LANGUAGES C CXX)
cmake_minimum_required(VERSION 3.4...3.18)
include(ExternalProject)

#set (CMAKE_CXX_STANDARD 17)

if(NOT CMAKE_BUILD_TYPE)
  set(CMAKE_BUILD_TYPE Release)
endif()

if (CMAKE_SOURCE_DIR STREQUAL CMAKE_BINARY_DIR ) 
  message (FATAL_ERROR
    "In-source builds are not allowed. Please clean your source tree and try again.")  
endif()

add_library(aiger_library aiger/aiger.h aiger/aiger.c)
target_compile_options(aiger_library PRIVATE -fPIC)

ExternalProject_Add(cadical_external
	SOURCE_DIR "${CMAKE_SOURCE_DIR}/cadical"
	CONFIGURE_COMMAND "CXXFLAGS=-fPIC" "${CMAKE_SOURCE_DIR}/cadical/configure"
	BUILD_COMMAND "make"
	BINARY_DIR "${CMAKE_SOURCE_DIR}/cadical/build/"
	INSTALL_COMMAND ""
)

add_library(cadical_library SHARED IMPORTED )
set_target_properties(cadical_library PROPERTIES IMPORTED_LOCATION "${CMAKE_SOURCE_DIR}/cadical/build/libcadical.a" )
add_dependencies(cadical_library cadical_external)

add_library(rsynth_library relationSynthesiser.h relationSynthesiser.cc)
target_link_libraries(rsynth_library PRIVATE cadical_library)
target_compile_options(rsynth_library PRIVATE -fPIC)

find_package(pybind11 CONFIG)
message(STATUS "Found pybind11 v${pybind11_VERSION}: ${pybind11_INCLUDE_DIRS}")
if (pybind11_FOUND) 
  pybind11_add_module(aiger SHARED aiger_bindings.cc)
  target_link_libraries(aiger PRIVATE aiger_library)
  target_include_directories(aiger PUBLIC "aiger")
  
  pybind11_add_module(cadical SHARED cadical_bindings.cc)
  target_link_libraries(cadical PRIVATE cadical_library)
  
  pybind11_add_module(relationSynthesiser SHARED relationSynthesiser_bindings.cc)
  target_link_libraries(relationSynthesiser PRIVATE rsynth_library)
endif()
