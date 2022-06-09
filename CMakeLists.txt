cmake_minimum_required(VERSION 3.4)
project(IPLFCPA)

# we need LLVM_HOME in order not automatically set LLVM_DIR
SET(CMAKE_C_COMPILER /usr/bin/clang-12)
SET(CMAKE_CXX_COMPILER /usr/bin/clang++-12)

find_package(LLVM REQUIRED CONFIG)
add_definitions(${LLVM_DEFINITIONS})
#add_definitions(-DIRMODEL -DANALYSIS)
add_definitions($ENV{FOO_VAR})
include_directories(${LLVM_INCLUDE_DIRS})
link_directories(${LLVM_LIBRARY_DIRS})

# add_library(Bprinter SHARED IMPORTED)
# set_target_properties(Bprinter PROPERTIES IMPORTED_LOCATION "/usr/local/lib/libbprinter.a")

include_directories("/usr/local/include/spatial")
include_directories("./include")
add_subdirectory(VascoLfcpaPass)  # Use your pass name here.
