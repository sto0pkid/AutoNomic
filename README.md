#Autonomous Nomic Overlay Network


Under development, expect bugs and please report any you find; AutoNomic can't be released until we're sure that it's bug-free. 

To run example: "./autonomic < examples/socrates"  

For verbose print: "./autonomic --level 100 < examples/socrates"  

###deps:  
apt-get install libboost-system-dev libboost-filesystem-dev libcurl4-openssl-dev    #todo:not all necessary, update  
####For building libmarpa
apt-get install -y build-essential autoconf automake libtool
####for the n3 parser:  
apt-get install libboost-regex-dev
apt-get install clang-3.6 libc++-dev  

C++ Compiler has to support C++11, gcc-4.9 and clang++-3.6 are known to work.  

Building: run make. You can also use cmake, but the hand-written Makefile is the primary method.  
