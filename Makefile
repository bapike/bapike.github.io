#!/usr/bin/make
# Most of the HTML of all of the pages will be identical.  Let's keep the common HTML in:
#   src/common-pre_title.htmlsnip
#   src/common-pre_content.htmlsnip
#   src/common-post_content.htmlsnip
# and then have, e.g.,
#   src/foo-title.htmlsnip
#   src/foo-content.htmlsnip
# Then "foo.htmlsnip" would be built by concatenating:
#   src/common-pre_title.htmlsnip
#   src/foo-title.htmlsnip
#   src/common-pre_content.htmlsnip
#   src/foo-content.htmlsnip
#   src/common-post_content.htmlsnip

SRCDIR=src

PRETITLE=$(SRCDIR)/common-1-pre_title.htmlsnip
PRECONTENT=$(SRCDIR)/common-2-pre_content.htmlsnip
POSTCONTENT=$(SRCDIR)/common-3-post_content.htmlsnip

COMMONDEPS=$(PRETITLE) $(PRECONTENT) $(POSTCONTENT) 

all: index.html about.html software.html teaching.html research.html test.html

# Unfortunately, this will add newlines at the end of each file, but there's no easy way around that 
%.html: $(COMMONDEPS) $(SRCDIR)/%.htmlsnip
	cp $(PRETITLE) $@
	head -n 1 $(SRCDIR)/$*.htmlsnip >> $@
	cat $(PRECONTENT) >> $@
	tail -n +2 $(SRCDIR)/$*.htmlsnip >> $@
	cat $(POSTCONTENT) >> $@

#cat $(PRETITLE) $(SRCDIR)/$*-title.htmlsnip $(PRECONTENT) $(SRCDIR)/$*-content.htmlsnip $(POSTCONTENT) > $@ 

clean:
	rm -f *.html

