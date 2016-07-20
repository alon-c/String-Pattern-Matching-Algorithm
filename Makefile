all: tester

tester: tester.c slist.c slist.h pattern_matching.c pattern_matching.h
	gcc -o tester tester.c slist.c pattern_matching.c 
