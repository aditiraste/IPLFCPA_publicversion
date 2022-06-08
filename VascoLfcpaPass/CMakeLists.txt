set(LLVM_LINK_COMPONENTS core support irreader passes transformutils)
add_executable(VascoLfcpaPass lfcpa.cpp)
# add_library(VascoLfcpaPass MODULE
#     # List your source files here.
#    # TransformIR.cpp
#      lfcpa.cpp
# )

# LLVM is (typically) built with no C++ RTTI. We need to match that;
# otherwise, we'll get linker errors about missing RTTI data.
set_target_properties(VascoLfcpaPass PROPERTIES
    COMPILE_FLAGS "-fno-rtti -g -O2 -std=c++14"
)

llvm_config (VascoLfcpaPass ${LLVM_LINK_COMPONENTS})

target_link_libraries(VascoLfcpaPass PRIVATE "/usr/local/lib/libSpatial.so")
