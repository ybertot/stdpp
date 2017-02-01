# Process flags
ifeq ($(Y), 1)
	YFLAG=-y
endif

# Configure Coq warnings
COQ_MAKEFILE_FLAGS ?= -arg -w -arg -notation-overridden,-redundant-canonical-projection,-several-object-files

# Forward most targets to Coq makefile (with some trick to make this phony)
%: Makefile.coq phony
	+@make -f Makefile.coq $@

all: Makefile.coq
	+@make -f Makefile.coq all

clean: Makefile.coq
	+@make -f Makefile.coq clean
	find theories \( -name "*.v.d" -o -name "*.vo" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vio" \) -print -delete
	rm -f Makefile.coq

# Create Coq Makefile. POSIX awk can't do in-place editing, but coq_makefile wants the real filename, so we do some file gymnastics.
Makefile.coq: _CoqProject Makefile awk.Makefile
	coq_makefile $(COQ_MAKEFILE_FLAGS) -f _CoqProject -o Makefile.coq
	mv Makefile.coq Makefile.coq.tmp && awk -f awk.Makefile Makefile.coq.tmp > Makefile.coq && rm Makefile.coq.tmp

# Install build-dependencies
build-dep:
	build/opam-pins.sh < opam.pins
	opam upgrade $(YFLAG) # it is not nice that we upgrade *all* packages here, but I found no nice way to upgrade only those that we pinned
	opam pin add coq-stdpp "$$(pwd)#HEAD" -k git -n -y
	opam install coq-stdpp --deps-only $(YFLAG)
	opam pin remove coq-stdpp

# Some files that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_CoqProject: ;
awk.Makefile: ;

# Phony targets (i.e. targets that should be run no matter the timestamps of the involved files)
phony: ;
.PHONY: all clean phony