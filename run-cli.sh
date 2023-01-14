#!/bin/bash

# Tilde will only be expanded once, so we can't give relative paths with tildes
java -classpath ./target/classes:`echo $HOME`/.m2/repository/org/parboiled/parboiled-core/1.4.1/parboiled-core-1.4.1.jar:`echo $HOME`/.m2/repository/org/parboiled/parboiled-java/1.4.1/parboiled-java-1.4.1.jar:`echo $HOME`/.m2/repository/org/ow2/asm/asm/7.1/asm-7.1.jar:`echo $HOME`/.m2/repository/org/ow2/asm/asm-tree/7.1/asm-tree-7.1.jar:`echo $HOME`/.m2/repository/org/ow2/asm/asm-analysis/7.1/asm-analysis-7.1.jar:`echo $HOME`/.m2/repository/org/ow2/asm/asm-util/7.1/asm-util-7.1.jar:`echo $HOME`/.m2/repository/org/sat4j/org.sat4j.core/2.3.1/org.sat4j.core-2.3.1.jar kodkod.cli.KodkodServer -stepper -temporal
