#!/usr/bin/env bash
add-apt-repository -y 'ppa:mhier/libboost-latest'
apt-get update
apt-get install -y boost1.74 clang-11 libc6-dev-i386
git submodule update --init
