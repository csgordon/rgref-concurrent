#!/bin/bash
export AUX="FinResults.v"
export CORE="RGref/DSL/LinearEnv.v RGref/DSL/DSL.v RGref/DSL/Theories.v \
             RGref/DSL/Core.v RGref/DSL/Monad.v RGref/DSL/Fields.v RGref/DSL/Concurrency.v"
export EXAMPLES="AppendOnlyLinkedList.v MonotonicCounter.v PrependOnlyPureList.v \
                 CounterModule.v RCC.v ReferenceImmutability.v IndIndLinkedList.v"
export CONC_EXAMPLES="AtomicCounter.v TrieberStack.v MichaelScottQ.v Hindsight.v UnionFind.v ProducerConsumer.v ProducerConsumerClient.v"
export BUGS="KnownUnsoundnessExamples.v"
#export TMP="Tracing.v"
coq_makefile -R RGref RGref $TMP $AUX $CORE $CONC_EXAMPLES > Makefile
touch .depend
make depend
make -j `nproc`
