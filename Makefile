all: pdf html
html:
	asciidoctor README.adoc -o index.html
pdf:
	asciidoctor-pdf -a allow-uri-read Readme.adoc -o SecurityScheme.pdf