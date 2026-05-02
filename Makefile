build:
	coq_makefile -f _CoqProject -o CoqMakefile
	make -f CoqMakefile

clean:
	make -f CoqMakefile clean
	rm -f CoqMakefile
