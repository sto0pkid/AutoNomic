MESSAGE( STATUS "note: you dont have to use cmake, our hand-written Makefile more-or-less works" )
MESSAGE( STATUS "" )

#cmake_minimum_required(VERSION 3.0)
cmake_minimum_required(VERSION 2.8.7)


project(autonomic)




SET (CMAKE_C_COMPILER             "/usr/bin/clang")
SET (CMAKE_CXX_COMPILER           "/usr/bin/clang++")#-libc++")
SET (CMAKE_AR      "/usr/bin/llvm-ar")
SET (CMAKE_LINKER  "/usr/bin/llvm-ld")
SET (CMAKE_NM      "/usr/bin/llvm-nm")
SET (CMAKE_OBJDUMP "/usr/bin/llvm-objdump")
SET (CMAKE_RANLIB  "/usr/bin/llvm-ranlib")


set(MARPA_DIST ${CMAKE_SOURCE_DIR}/libmarpa/dist/)



set(CMAKE_CXX_FLAGS "${CMAKE_CXX_FLAGS} -std=c++11 -Wall -Wextra -ggdb -g")# -stdlib=libc++ 
set(ASAN "-fsanitize-undefined-trap-on-error -fsanitize=address -fsanitize=integer -fsanitize=unsigned-integer-overflow ")
set(COMMON_FLAGS "-I${Boost_INCLUDE_DIRS} ${CMAKE_CXX_FLAGS}  -I${MARPA_DIST} -Dwith_marpa -DJSON  ")


set(SOURCE_FILES
    jsonld_an.cpp
    jsonld_an.h
    jsonld.cpp
    jsonld.h
    json_spirit.h
    misc.cpp
    misc.h
    nquads.cpp
    unifiers.cpp
    json_object.cpp
    json_object.h
    prover.cpp
    prover.h
    rdf.cpp
    rdf.h
    strings.h
    autonomic.cpp
    univar.cpp
    univar.h
    marpa_an.cpp
)


find_package(Boost REQUIRED regex)

add_executable(autonomic ${SOURCE_FILES})
add_executable(autonomic-moderate ${SOURCE_FILES})
add_executable(autonomic-moderate0 ${SOURCE_FILES})
add_executable(autonomic-asan ${SOURCE_FILES})
add_executable(autonomic3 ${SOURCE_FILES})
add_executable(autonomic3-asan ${SOURCE_FILES})
add_executable(autonomicd3 ${SOURCE_FILES})
add_executable(autonomicd3-asan ${SOURCE_FILES})


SET_TARGET_PROPERTIES(autonomic   PROPERTIES COMPILE_FLAGS "${COMMON_FLAGS} -DDEBUG -O0")
SET_TARGET_PROPERTIES(autonomic-moderate   PROPERTIES COMPILE_FLAGS "${COMMON_FLAGS} -O1")
SET_TARGET_PROPERTIES(autonomic-moderate0   PROPERTIES COMPILE_FLAGS "${COMMON_FLAGS} -O0")
SET_TARGET_PROPERTIES(autonomic-asan   PROPERTIES COMPILE_FLAGS "${COMMON_FLAGS} -DDEBUG -O0  ${ASAN}")
SET_TARGET_PROPERTIES(autonomic3  PROPERTIES COMPILE_FLAGS "${COMMON_FLAGS} -O3")
SET_TARGET_PROPERTIES(autonomic3-asan  PROPERTIES COMPILE_FLAGS "${COMMON_FLAGS} -O3 ${ASAN}")
SET_TARGET_PROPERTIES(autonomicd3 PROPERTIES COMPILE_FLAGS "${COMMON_FLAGS} -DDEBUG -O3")
SET_TARGET_PROPERTIES(autonomicd3-asan PROPERTIES COMPILE_FLAGS "${COMMON_FLAGS} -DDEBUG -O3 ${ASAN}")

#set(LIBSS "")

target_link_libraries(autonomic            PRIVATE ${Boost_LIBRARIES} ${CMAKE_DL_LIBS} -L${MARPA_DIST}/.libs -lmarpa)
target_link_libraries(autonomic-moderate            PRIVATE ${Boost_LIBRARIES} ${CMAKE_DL_LIBS} "-L${MARPA_DIST}/.libs -lmarpa")
target_link_libraries(autonomic-moderate0            PRIVATE ${Boost_LIBRARIES} ${CMAKE_DL_LIBS} "-L${MARPA_DIST}/.libs -lmarpa")
target_link_libraries(autonomic3           PRIVATE ${Boost_LIBRARIES} ${CMAKE_DL_LIBS} "-L${MARPA_DIST}/.libs -lmarpa")
target_link_libraries(autonomic-asan            PRIVATE ${Boost_LIBRARIES} ${CMAKE_DL_LIBS} "-L${MARPA_DIST}/.libs -lmarpa")
target_link_libraries(autonomic-asan           PRIVATE ${Boost_LIBRARIES} ${CMAKE_DL_LIBS} "-L${MARPA_DIST}/.libs -lmarpa")
target_link_libraries(autonomicd3          PRIVATE ${Boost_LIBRARIES} ${CMAKE_DL_LIBS} "-L${MARPA_DIST}/.libs -lmarpa")
target_link_libraries(autonomicd3-asan          PRIVATE ${Boost_LIBRARIES} ${CMAKE_DL_LIBS} "-L${MARPA_DIST}/.libs -lmarpa"  )
#target_include_directories(m-autonomic PRIVATE ${Boost_INCLUDE_DIRS} ${MARPA_DIST})
#target_include_directories(  autonomic PRIVATE ${Boost_INCLUDE_DIRS})



#<ngladitz> http://pastebin.com/Tm5AYHEg ... I added boost and dl and redid the source file listing to make it build (I didn't have a marpa.cpp) ... I don't really know what belongs where source file wise but it produces a binary :)
#<ngladitz> cmake 3.1 adds support for selection of language standards (though I would require 3.2 for it) which would make the -std=c++11 superfluous ... which in turn would make the build more portable
