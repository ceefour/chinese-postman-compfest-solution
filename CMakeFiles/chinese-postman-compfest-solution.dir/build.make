# CMAKE generated file: DO NOT EDIT!
# Generated by "Unix Makefiles" Generator, CMake Version 3.17

# Delete rule output on recipe failure.
.DELETE_ON_ERROR:


#=============================================================================
# Special targets provided by cmake.

# Disable implicit rules so canonical targets will work.
.SUFFIXES:


# Disable VCS-based implicit rules.
% : %,v


# Disable VCS-based implicit rules.
% : RCS/%


# Disable VCS-based implicit rules.
% : RCS/%,v


# Disable VCS-based implicit rules.
% : SCCS/s.%


# Disable VCS-based implicit rules.
% : s.%


.SUFFIXES: .hpux_make_needs_suffix_list


# Command-line flag to silence nested $(MAKE).
$(VERBOSE)MAKESILENT = -s

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
CMAKE_COMMAND = /home/linuxbrew/.linuxbrew/Cellar/cmake/3.17.3/bin/cmake

# The command to remove a file.
RM = /home/linuxbrew/.linuxbrew/Cellar/cmake/3.17.3/bin/cmake -E rm -f

# Escaping for special characters.
EQUALS = =

# The top-level source directory on which CMake was run.
CMAKE_SOURCE_DIR = /workspace/chinese-postman-compfest-solution

# The top-level build directory on which CMake was run.
CMAKE_BINARY_DIR = /workspace/chinese-postman-compfest-solution

# Include any dependencies generated for this target.
include CMakeFiles/chinese-postman-compfest-solution.dir/depend.make

# Include the progress variables for this target.
include CMakeFiles/chinese-postman-compfest-solution.dir/progress.make

# Include the compile flags for this target's objects.
include CMakeFiles/chinese-postman-compfest-solution.dir/flags.make

CMakeFiles/chinese-postman-compfest-solution.dir/main.cpp.o: CMakeFiles/chinese-postman-compfest-solution.dir/flags.make
CMakeFiles/chinese-postman-compfest-solution.dir/main.cpp.o: main.cpp
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --progress-dir=/workspace/chinese-postman-compfest-solution/CMakeFiles --progress-num=$(CMAKE_PROGRESS_1) "Building CXX object CMakeFiles/chinese-postman-compfest-solution.dir/main.cpp.o"
	/usr/bin/c++  $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -o CMakeFiles/chinese-postman-compfest-solution.dir/main.cpp.o -c /workspace/chinese-postman-compfest-solution/main.cpp

CMakeFiles/chinese-postman-compfest-solution.dir/main.cpp.i: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Preprocessing CXX source to CMakeFiles/chinese-postman-compfest-solution.dir/main.cpp.i"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -E /workspace/chinese-postman-compfest-solution/main.cpp > CMakeFiles/chinese-postman-compfest-solution.dir/main.cpp.i

CMakeFiles/chinese-postman-compfest-solution.dir/main.cpp.s: cmake_force
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green "Compiling CXX source to assembly CMakeFiles/chinese-postman-compfest-solution.dir/main.cpp.s"
	/usr/bin/c++ $(CXX_DEFINES) $(CXX_INCLUDES) $(CXX_FLAGS) -S /workspace/chinese-postman-compfest-solution/main.cpp -o CMakeFiles/chinese-postman-compfest-solution.dir/main.cpp.s

# Object files for target chinese-postman-compfest-solution
chinese__postman__compfest__solution_OBJECTS = \
"CMakeFiles/chinese-postman-compfest-solution.dir/main.cpp.o"

# External object files for target chinese-postman-compfest-solution
chinese__postman__compfest__solution_EXTERNAL_OBJECTS =

chinese-postman-compfest-solution: CMakeFiles/chinese-postman-compfest-solution.dir/main.cpp.o
chinese-postman-compfest-solution: CMakeFiles/chinese-postman-compfest-solution.dir/build.make
chinese-postman-compfest-solution: CMakeFiles/chinese-postman-compfest-solution.dir/link.txt
	@$(CMAKE_COMMAND) -E cmake_echo_color --switch=$(COLOR) --green --bold --progress-dir=/workspace/chinese-postman-compfest-solution/CMakeFiles --progress-num=$(CMAKE_PROGRESS_2) "Linking CXX executable chinese-postman-compfest-solution"
	$(CMAKE_COMMAND) -E cmake_link_script CMakeFiles/chinese-postman-compfest-solution.dir/link.txt --verbose=$(VERBOSE)

# Rule to build all files generated by this target.
CMakeFiles/chinese-postman-compfest-solution.dir/build: chinese-postman-compfest-solution

.PHONY : CMakeFiles/chinese-postman-compfest-solution.dir/build

CMakeFiles/chinese-postman-compfest-solution.dir/clean:
	$(CMAKE_COMMAND) -P CMakeFiles/chinese-postman-compfest-solution.dir/cmake_clean.cmake
.PHONY : CMakeFiles/chinese-postman-compfest-solution.dir/clean

CMakeFiles/chinese-postman-compfest-solution.dir/depend:
	cd /workspace/chinese-postman-compfest-solution && $(CMAKE_COMMAND) -E cmake_depends "Unix Makefiles" /workspace/chinese-postman-compfest-solution /workspace/chinese-postman-compfest-solution /workspace/chinese-postman-compfest-solution /workspace/chinese-postman-compfest-solution /workspace/chinese-postman-compfest-solution/CMakeFiles/chinese-postman-compfest-solution.dir/DependInfo.cmake --color=$(COLOR)
.PHONY : CMakeFiles/chinese-postman-compfest-solution.dir/depend

