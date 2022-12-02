# AutoNomic

A p2p nomic game.

### Dependencies
```apt-get install libboost-system-dev libboost-filesystem-dev libcurl4-openssl-dev```


#### For building libmarpa
```apt-get install -y build-essential autoconf automake libtool```

#### For the n3 parser:
```apt-get install libboost-regex-dev apt-get install clang-3.6 libc++-dev```

C++ Compiler has to support C++11, gcc-4.9 and clang++-3.6 are known to work.

### Building

```make```

You can also use cmake, but the hand-written Makefile is the primary method.


### Running

```./autonomic < tests/examples/socrates```

For verbose print: 

```./autonomic --level 100 < tests/examples/socrates```

### Development discussion
* IRC Freenode ```#AutoNomic```
* Discord server ```frdcsa-logicmoo-agi```, channel [```#frdcsa-tau```](https://discord.com/channels/748871194572226661/766281237722824714)