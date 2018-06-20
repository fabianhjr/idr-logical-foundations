default : test pdf

all : test pdf epub

test :
	idris --check --total book/*.lidr

pdf :
	$(pandoc_cmd) -o 'Logical Foundations in Idris.pdf' \
	$(book)

epub :
	$(pandoc_cmd) -o 'Logical Foundations in Idris.epub' \
	$(book)



pandoc_cmd = pandoc -f markdown+lhs --pdf-engine=xelatex \
--top-level-division=chapter --strip-comments

book = book/book.md book/*.lidr
