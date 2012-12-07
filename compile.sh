#!/bin/bash
export CORE="RGref/DSL/LinearEnv.v RGref/DSL/DSL.v RGref/DSL/Theories.v RGref/DSL/Core.v RGref/DSL/Monad.v"
export EXAMPLES="AppendOnlyLinkedList.v MonotonicCounter.v PrependOnlyPureList.v CounterModule.v RCC.v ReferenceImmutability.v LinkedList.v"
coq_makefile -arg -impredicative-set -R RGref RGref $CORE $EXAMPLES > Makefile
touch .depend
make depend
make
