# -*- Makefile -*-

# --------------------------------------------------------------------
.PHONY: default build clean install

default: build

build:
	dune build

clean:
	dune clean

install:
	dune install
