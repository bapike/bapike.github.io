###What is this?
This is my (simple) website, http://www.brianpike.info/.

Since lots of HTML is shared between web pages, I've put all the parts
in `src/` and actually build the site using the `Makefile`.  The
`src/common*.htmlsnip` files are the common bits of the HTML files.
Each `src/foo.htmlsnip` will be used to generate `foo.html` in the
following manner: the **first line** contains the title of the web
page, and **the rest of the file** is inserted as the content of the
page.


###How do I make `vim` use HTML syntax highlighting for `.htmlsnip` files?
Add this to your `.vimrc`:
```
" associate *.htmlsnip with html filetype
au BufRead,BufNewFile *.htmlsnip setfiletype html
```
