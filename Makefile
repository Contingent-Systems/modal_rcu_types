################################
## Latex Sources and style files
################################

# Name of the main tex file without extension
PROJECT = paper

# Style file or list of files
#STYFILE = lipics-v2016.sty

## Directories to search for sources

APPENDICESDIR = appendices
CHAPTERSDIR = chapters
TABLESDIR = tables
FIGURESDIR = figures
REFERENCESDIR = references

## Search for sources

# Directories to search for .tex files.
TEXDIRS = $(wildcard $(APPENDICESDIR) $(CHAPTERSDIR) $(TABLESDIR))

# Find .tex files in the subdirectories
# performing a search of *.tex files amongst all the directories defined on $TEXDIRS
TEXTARGETS = $(if $(TEXDIRS),$(shell find $(TEXDIRS) -type f -name "*.tex"),)

## Search for images

# Search for changes on png figures. This can be changed by changing the figure extension or by adding
# other search pattern for other image extensions.
FIGURETARGETS = $(if $(wildcard $(FIGURESDIR)),$(shell find $(FIGURESDIR) -type f -name "*.pdf"),)

## Build the final target

# Global set of targets.
# This searches changes on the $PROJECT.tex file, the template $STYFILE (or set of files)
# and the .tex files found on the subdirectories by $TEXTARGETS
TARGETS = $(PROJECT).tex $(TEXTARGETS) $(FIGURETARGETS)
#TARGETS = $(PROJECT).tex $(STYFILE) $(TEXTARGETS) $(FIGURETARGETS)

######################
## Compilation Options
######################

# Command to compile latex source
TEX = pdflatex

# Command to compile bibliography using bibtex
BIBTEX = bibtex

# Command to build index
MAKEIDX = makeindex

# Build the list of symbols for the project. The file nomencl.ist is temporary and
# the name is unimportant.
# The paper does not currently load nomencl, so no .nlo is emitted; skip the step
# rather than failing the build when it is absent.
BUILDSYMBOLS = [ -f $(PROJECT).nlo ] && $(MAKEIDX) $(PROJECT).nlo -s nomencl.ist -o $(PROJECT).nls || true

# Commmand to build the latex project into PDF (or DVI according to $(TEX).
BUILDTEX = $(TEX) $(PROJECT).tex

# When using vim-latexsuite it adds annoying <++> symbols, this removes that shit from all .tex files
CLEANEQS = grep -lr --include=*.tex '<++>' ./ | xargs sed -i 's/<++>//g'


##############################
## DEFINING TARGETS OPERATIONS
##############################

#all: $(PROJECT).pdf
all: bibliography

$(PROJECT).pdf: $(TARGETS)
	#$(CLEANEQS)
	$(BUILDTEX)
	$(BUILDSYMBOLS)
	$(BUILDTEX)
	$(BUILDTEX)
	#make clean

bibliography: $(TARGETS) 
	#$(CLEANEQS)
	$(BUILDTEX)
	$(BUILDSYMBOLS)
	$(BIBTEX) $(PROJECT)
	$(BUILDTEX)
	$(BUILDTEX)
	$(BUILDTEX)
	#make clean

# Clean all temporary resource files created during the compilation of the master file
clean:
	rm -f *.log *.bak *.aux *.bbl *.blg *.idx *.toc *.out *~ *.lof *.lot *.nlo *.nls *.ist *.ilg
	rm -f $(CHAPTERSDIR)/*.log $(CHAPTERSDIR)/*.bak $(CHAPTERSDIR)/*.aux $(CHAPTERSDIR)/*.bbl $(CHAPTERSDIR)/*.blg $(CHAPTERSDIR)/*.idx $(CHAPTERSDIR)/*.toc $(CHAPTERSDIR)/*.out $(CHAPTERSDIR)/*~  $(CHAPTERSDIR)/*.nlo $(CHAPTERSDIR)/*.nls $(CHAPTERSDIR)/*.ist $(CHAPTERSDIR)/*.ilg
	rm -f $(TABLESDIR)/*.log $(TABLESDIR)/*.bak $(TABLESDIR)/*.aux $(TABLESDIR)/*.bbl $(TABLESDIR)/*.blg $(TABLESDIR)/*.idx $(TABLESDIR)/*.toc $(TABLESDIR)/*.out $(TABLESDIR)/*~ $(TABLESDIR)/*.nlo $(TABLESDIR)/*.nls $(TABLESDIR)/*.ist $(TABLESDIR)/*.ilg
	rm -f $(APPENDICESDIR)/*.log $(APPENDICESDIR)/*.bak $(APPENDICESDIR)/*.aux $(APPENDICESDIR)/*.bbl $(APPENDICESDIR)/*.blg $(APPENDICESDIR)/*.idx $(APPENDICESDIR)/*.toc $(APPENDICESDIR)/*.out $(APPENDICESDIR)/*~ $(APPENDICESDIR)/*.nlo $(APPENDICESDIR)/*.nls $(APPENDICESDIR)/*.ist $(APPENDICESDIR)/*.ilg

# Clean all temporary resource files created during compilation and delete the latex output.
clean-all:
	rm -f *.dvi *.log *.bak *.aux *.bbl *.blg *.idx *.ps *.eps $(PROJECT).pdf *.toc *.out *~ *.lof *.lot *.nlo *.nls *.ist *.ilg
	rm -f $(CHAPTERSDIR)/*.dvi $(CHAPTERSDIR)/*.log $(CHAPTERSDIR)/*.bak $(CHAPTERSDIR)/*.aux $(CHAPTERSDIR)/*.bbl $(CHAPTERSDIR)/*.blg $(CHAPTERSDIR)/*.idx $(CHAPTERSDIR)/*.ps $(CHAPTERSDIR)/*.eps $(CHAPTERSDIR)/*.pdf $(CHAPTERSDIR)/*.toc $(CHAPTERSDIR)/*.out $(CHAPTERSDIR)/*~  $(CHAPTERSDIR)/*.nlo $(CHAPTERSDIR)/*.nls $(CHAPTERSDIR)/*.ist $(CHAPTERSDIR)/*.ilg
	rm -f $(TABLESDIR)/*.dvi $(TABLESDIR)/*.log $(TABLESDIR)/*.bak $(TABLESDIR)/*.aux $(TABLESDIR)/*.bbl $(TABLESDIR)/*.blg $(TABLESDIR)/*.idx $(TABLESDIR)/*.ps $(TABLESDIR)/*.eps $(TABLESDIR)/*.pdf $(TABLESDIR)/*.toc $(TABLESDIR)/*.out $(TABLESDIR)/*~ $(TABLESDIR)/*.nlo $(TABLESDIR)/*.nls $(TABLESDIR)/*.ist $(TABLESDIR)/*.ilg
	rm -f $(APPENDICESDIR)/*.dvi $(APPENDICESDIR)/*.log $(APPENDICESDIR)/*.bak $(APPENDICESDIR)/*.aux $(APPENDICESDIR)/*.bbl $(APPENDICESDIR)/*.blg $(APPENDICESDIR)/*.idx $(APPENDICESDIR)/*.ps $(APPENDICESDIR)/*.eps $(APPENDICESDIR)/*.pdf $(APPENDICESDIR)/*.toc $(APPENDICESDIR)/*.out $(APPENDICESDIR)/*~ $(APPENDICESDIR)/*.nlo $(APPENDICESDIR)/*.nls $(APPENDICESDIR)/*.ist $(APPENDICESDIR)/*.ilg

# When using vim-latexsuite it adds annoying <++> symbols, this removes that shit from all .tex files
# by calling the predefined command above.
clean-eqs:
	$(CLEANEQS)
