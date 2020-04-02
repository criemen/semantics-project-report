#!/bin/bash
echo "hi from script"
 for i; do 
    echo $i 
 done
 echo `pwd`
mkdir codeql-dimp.testproj/src/
touch codeql-dimp.testproj/src/testfile.dimp
cp -R db codeql-dimp.testproj/db-generate_trap

#./generate_trap.py
 #/home/