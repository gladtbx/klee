//===-- KInstIterator.h -----------------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Internal/Module/KInstruction.h"
#include "llvm/Instruction.h"
#include "llvm/BasicBlock.h"
#include "llvm/Function.h"

#ifndef KLEE_KINSTITERATOR_H
#define KLEE_KINSTITERATOR_H

namespace klee {
  struct KInstruction;

  class KInstIterator {
    KInstruction **it;

  public:
    KInstIterator() : it(0) {}
    KInstIterator(KInstruction **_it) : it(_it) {}

    bool operator==(const KInstIterator &b) const {
      return it==b.it;
    }
    bool operator!=(const KInstIterator &b) const {
      return !(*this == b);
    }

    KInstIterator &operator++() {
      ++it;
      return *this;
    }

    operator KInstruction*() const { return it ? *it : 0;}
    operator bool() const { return it != 0; }

    KInstruction *operator ->() const { return *it; }
    std::string getFuncName() const{
    	return (*it)->inst->getParent()->getParent()->getNameStr();
    }
  };
} // End klee namespace

#endif
