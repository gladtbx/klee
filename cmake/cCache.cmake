#===------------------------------------------------------------------------===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#

#find_package(GREEN)
# Set the default so that if the following is true:
# * Z3 was found
# * ENABLE_SOLVER_Z3 is not already set as a cache variable
#
# then the default is set to `ON`. Otherwise set the default to `OFF`.
# A consequence of this is if we fail to detect Z3 the first time
# subsequent calls to CMake will not change the default.

if (ENABLE_SOLVER_CCACHE)
  message(STATUS "CCACHE solver support enabled")
    set(ENABLE_CCACHE 1) # For config.h

else()
  message(STATUS "CCACHE solver support disabled")
    set(ENABLE_CCACHE 0) # For config.h
endif()
