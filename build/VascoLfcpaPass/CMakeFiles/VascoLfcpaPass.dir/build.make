# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.16

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Remove some rules from gmake that .SUFFIXES does not remove.
SUFFIXES =

.SUFFIXES: .hpux_make_needs_suffix_list


# Suppress display of executed commands.
$(VERBOSE).SILENT:


# A target that is always out of date.
cmake_force:

.PHONY : cmake_force

#=============================================================================
# Set environment variables for the build.

# The shell in which to execute make rules.
SHELL = /bin/sh

# The CMake executable.
CMAKE_COMMAND = /usr/bin/cmake

# The command to remove a file.
RM = /usr/bin/cmake -E remove -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /mnt/d/MTP/IPLFCPA

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /mnt/d/MTP/IPLFCPA/build

# Include any dependencies generated for this target.
include VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/depend.make

# Include the progress variables for this target.
include VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/progress.make

# Include the compile flags for this target's objects.
include VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/flags.make

VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.o: VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/flags.make
VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.o: ../VascoLfcpaPass/lfcpa.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/mnt/d/MTP/IPLFCPA/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.o"
	cd /mnt/d/MTP/IPLFCPA/build/VascoLfcpaPass && /usr/bin/clang++-12  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.o -c /mnt/d/MTP/IPLFCPA/VascoLfcpaPass/lfcpa.cpp

VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.i"
	cd /mnt/d/MTP/IPLFCPA/build/VascoLfcpaPass && /usr/bin/clang++-12 $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /mnt/d/MTP/IPLFCPA/VascoLfcpaPass/lfcpa.cpp > CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.i

VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.s"
	cd /mnt/d/MTP/IPLFCPA/build/VascoLfcpaPass && /usr/bin/clang++-12 $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /mnt/d/MTP/IPLFCPA/VascoLfcpaPass/lfcpa.cpp -o CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.s

# Object files for target VascoLfcpaPass
VascoLfcpaPass_OBJECTS = \
"CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.o"

# External object files for target VascoLfcpaPass
VascoLfcpaPass_EXTERNAL_OBJECTS =

VascoLfcpaPass/VascoLfcpaPass: VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.o
VascoLfcpaPass/VascoLfcpaPass: VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/build.make
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMCore.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMSupport.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMIRReader.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMPasses.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMTransformUtils.a
VascoLfcpaPass/VascoLfcpaPass: /usr/local/lib/libSpatial.so
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMCoroutines.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMHelloNew.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMipo.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMIRReader.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMAsmParser.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMBitWriter.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMFrontendOpenMP.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMLinker.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMObjCARCOpts.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMScalarOpts.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMAggressiveInstCombine.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMInstCombine.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMTarget.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMVectorize.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMInstrumentation.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMTransformUtils.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMAnalysis.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMObject.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMBitReader.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMMCParser.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMTextAPI.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMProfileData.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMCore.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMRemarks.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMBitstreamReader.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMMC.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMBinaryFormat.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMDebugInfoCodeView.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMDebugInfoMSF.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMSupport.a
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/x86_64-linux-gnu/libz.so
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/x86_64-linux-gnu/libtinfo.so
VascoLfcpaPass/VascoLfcpaPass: /usr/lib/llvm-12/lib/libLLVMDemangle.a
VascoLfcpaPass/VascoLfcpaPass: VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/mnt/d/MTP/IPLFCPA/build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX executable VascoLfcpaPass"
	cd /mnt/d/MTP/IPLFCPA/build/VascoLfcpaPass && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/VascoLfcpaPass.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/build: VascoLfcpaPass/VascoLfcpaPass

.PHONY : VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/build

VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/clean:
	cd /mnt/d/MTP/IPLFCPA/build/VascoLfcpaPass && $(CMAKE_COMMAND) -P CMakeFiles/VascoLfcpaPass.dir/cmake_clean.cmake
.PHONY : VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/clean

VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/depend:
	cd /mnt/d/MTP/IPLFCPA/build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /mnt/d/MTP/IPLFCPA /mnt/d/MTP/IPLFCPA/VascoLfcpaPass /mnt/d/MTP/IPLFCPA/build /mnt/d/MTP/IPLFCPA/build/VascoLfcpaPass /mnt/d/MTP/IPLFCPA/build/VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/depend
