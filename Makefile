all : test pdf

test :
	idris --noprelude --check --total src/*.lidr

pdf :
	pandoc -f markdown+lhs -o 'Logical Foundations in Idris.pdf' \
	--top-level-division=chapter --strip-comments \
	src/book.md src/*.lidr
