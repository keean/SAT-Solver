all : sat

sat: sat.cpp profile.h Parser-Combinators/parser_simple.hpp
	clang++ -ggdb -march=native -O3 -flto -std=gnu++11 -o sat sat.cpp 

