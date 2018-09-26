# -*- Makefile -*-

# --------------------------------------------------------------------
SUBDIRS  :=

include Makefile.common

# --------------------------------------------------------------------
.PHONY: install

install:
	$(MAKE) -f Makefile.coq install

# --------------------------------------------------------------------
this-clean::
	rm -f */.*.aux

this-distclean::
	rm -f $(shell find . -name '*~')

# --------------------------------------------------------------------
.PHONY: html

COQDOCJS    := coqdocjs
COQDOCFLAGS := \
  -R . xhl --html --interpolate \
  --external 'http://math-comp.github.io/math-comp/htmldoc/' mathcomp \
  --index indexpage --no-lib-name --parse-comments \
  --with-header $(COQDOCJS)/extra/header.html \
  --with-footer $(COQDOCJS)/extra/footer.html

export COQDOCFLAGS

html: config build
	rm -rf html && $(COQMAKE) html
	cp $(COQDOCJS)/extra/resources/* html

# --------------------------------------------------------------------
.PHONY: count dist

# --------------------------------------------------------------------
DISTDIR = xhl
TAROPT  = --posix --owner=0 --group=0

dist:
	if [ -e $(DISTDIR) ]; then rm -rf $(DISTDIR); fi
	./scripts/distribution.py $(DISTDIR) MANIFEST
	BZIP2=-9 tar $(TAROPT) -cjf $(DISTDIR).tar.bz2 $(DISTDIR)
	rm -rf $(DISTDIR)

count:
	@coqwc $(shell fgrep .v _CoqProject) | tail -1 | \
	  awk '{printf ("%d (spec=%d+proof=%d)\n", $$1+$$2, $$1, $$2)}'
