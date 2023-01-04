all: pdf html
html:
	asciidoctor README.adoc
pdf:
	asciidoctor-pdf -a allow-uri-read Readme.adoc