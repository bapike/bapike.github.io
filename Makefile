#!/usr/bin/make
# Most of the HTML of all of the pages will be identical.  Let's keep the common HTML in:
#   src/common-1-pre_title.htmlsnip
#   src/common-2-pre_content.htmlsnip
#   src/common-3-post_content.htmlsnip
# and then have, e.g.,
#   src/foo.htmlsnip
# Then "foo.html" is built by concatenating:
#   src/common-1-pre_title.htmlsnip
#   the first line of src/foo.htmlsnip
#   src/common-2-pre_content.htmlsnip
#   the rest of src/foo.htmlsnip
#   src/common-3-post_content.htmlsnip

SRCDIR=src

PRETITLE=$(SRCDIR)/common-1-pre_title.htmlsnip
PRECONTENT=$(SRCDIR)/common-2-pre_content.htmlsnip
POSTCONTENT=$(SRCDIR)/common-3-post_content.htmlsnip

COMMONDEPS=$(PRETITLE) $(PRECONTENT) $(POSTCONTENT) 

TARGETS=index.html about.html software.html teaching.html research.html test.html

all: $(TARGETS)

# Unfortunately, this will add newlines at the end of each file, but there's no easy way around that 
%.html: $(COMMONDEPS) $(SRCDIR)/%.htmlsnip
	cp $(PRETITLE) $@
	head -n 1 $(SRCDIR)/$*.htmlsnip >> $@
	cat $(PRECONTENT) >> $@
	tail -n +2 $(SRCDIR)/$*.htmlsnip >> $@
	cat $(POSTCONTENT) >> $@

clean:
	rm -f $(TARGETS)

add:
	git add $(TARGETS)

help:
	@ echo "Possible targets:"
	@ echo "all                  Build all the autobuilt HTML files"
	@ echo "foo.html             Build foo.html"
	@ echo "add                  \"git add\" all of the autobuilt HTML files"
	@ echo "clean                Delete all built products"
	@ echo "help                 Ask for help"

