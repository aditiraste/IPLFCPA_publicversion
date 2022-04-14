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
CMAKE_SOURCE_DIR = /home/ayush/Desktop/MTP/IPLFCPA

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /home/ayush/Desktop/MTP/IPLFCPA/_build

# Include any dependencies generated for this target.
include VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/depend.make

# Include the progress variables for this target.
include VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/progress.make

# Include the compile flags for this target's objects.
include VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/flags.make

VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.o: VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/flags.make
VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.o: ../VascoLfcpaPass/lfcpa.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/home/ayush/Desktop/MTP/IPLFCPA/_build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.o"
	cd /home/ayush/Desktop/MTP/IPLFCPA/_build/VascoLfcpaPass && /usr/bin/clang++-12  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.o -c /home/ayush/Desktop/MTP/IPLFCPA/VascoLfcpaPass/lfcpa.cpp

VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.i"
	cd /home/ayush/Desktop/MTP/IPLFCPA/_build/VascoLfcpaPass && /usr/bin/clang++-12 $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /home/ayush/Desktop/MTP/IPLFCPA/VascoLfcpaPass/lfcpa.cpp > CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.i

VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.s"
	cd /home/ayush/Desktop/MTP/IPLFCPA/_build/VascoLfcpaPass && /usr/bin/clang++-12 $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /home/ayush/Desktop/MTP/IPLFCPA/VascoLfcpaPass/lfcpa.cpp -o CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.s

# Object files for target VascoLfcpaPass
VascoLfcpaPass_OBJECTS = \
"CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.o"

# External object files for target VascoLfcpaPass
VascoLfcpaPass_EXTERNAL_OBJECTS =

VascoLfcpaPass/libVascoLfcpaPass.so: VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/lfcpa.cpp.o
VascoLfcpaPass/libVascoLfcpaPass.so: VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/build.make
VascoLfcpaPass/libVascoLfcpaPass.so: VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/home/ayush/Desktop/MTP/IPLFCPA/_build/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX shared module libVascoLfcpaPass.so"
	cd /home/ayush/Desktop/MTP/IPLFCPA/_build/VascoLfcpaPass && $(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/VascoLfcpaPass.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/build: VascoLfcpaPass/libVascoLfcpaPass.so

.PHONY : VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/build

VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/clean:
	cd /home/ayush/Desktop/MTP/IPLFCPA/_build/VascoLfcpaPass && $(CMAKE_COMMAND) -P CMakeFiles/VascoLfcpaPass.dir/cmake_clean.cmake
.PHONY : VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/clean

VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/depend:
	cd /home/ayush/Desktop/MTP/IPLFCPA/_build && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /home/ayush/Desktop/MTP/IPLFCPA /home/ayush/Desktop/MTP/IPLFCPA/VascoLfcpaPass /home/ayush/Desktop/MTP/IPLFCPA/_build /home/ayush/Desktop/MTP/IPLFCPA/_build/VascoLfcpaPass /home/ayush/Desktop/MTP/IPLFCPA/_build/VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : VascoLfcpaPass/CMakeFiles/VascoLfcpaPass.dir/depend

