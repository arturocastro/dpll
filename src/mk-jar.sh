#!/bin/sh

# test the input and setup the class name
class=DPLL

if [ "$#" -eq 1 ]; then
	class=$1
fi

# create manifest
echo Manifest-Version: 1.0> m.mf
echo Class-Path: .>> m.mf
echo Main-Class: $class>>m.mf
echo>>m.mf

javac *.java

jar cvfm $class.jar m.mf *.class

rm -f m.mf

cp $class.jar ../dpll-tests/DPLLN.jar
