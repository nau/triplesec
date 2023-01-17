all: pdf html
html:
	asciidoctor TripleSec.adoc -o index.html
	asciidoctor Howto.adoc -o Howto.html
pdf:
	asciidoctor-pdf -a allow-uri-read TripleSec.adoc -o TripleSec.pdf