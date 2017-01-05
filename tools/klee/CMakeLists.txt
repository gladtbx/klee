#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#
add_executable(klee
  main.cpp
)


# FIXME: This shouldn't be done here. Instead the KLEE libraries
# should declare their LLVM dependencies.
set(LLVM_COMPONENTS
	bitreader
	bitwriter
	engine
	ipo
	linker
	support
)

target_link_libraries(klee ${KLEE_LIBS})

install(TARGETS klee RUNTIME DESTINATION bin)

# The KLEE binary depends on the runtimes
add_dependencies(klee BuildKLEERuntimes)
