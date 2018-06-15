all : test pdf

test :
	idris --noprelude --check --total book/*.lidr

pdf :
	pandoc -f markdown+lhs -o 'Logical Foundations in Idris.pdf' \
	--top-level-division=chapter --strip-comments \
	book/book.md book/*.lidr
