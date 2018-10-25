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
TEXDIRS = $(APPENDICESDIR) $(CHAPTERSDIR) $(TABLESDIR)

# Find .tex files in the subdirectories
# performing a search of *.tex files amongst all the directories defined on $TEXDIRS
TEXTARGETS = $(shell find $(TEXDIRS) -type f -regex ".*\.\tex") 

## Search for images

# Search for changes on png figures. This can be changed by changing the figure extension or by adding
# other search pattern for other image extensions.
FIGURETARGETS = $(shell find $(FIGURESFDIR) -type f -regex ".*\.\pdf")

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
BUILDSYMBOLS = $(MAKEIDX) $(PROJECT).nlo -s nomencl.ist -o $(PROJECT).nls 

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
	rm -f $(TABLES)/*.log $(TABLES)/*.bak $(TABLES)/*.aux $(TABLES)/*.bbl $(TABLES)/*.blg $(TABLES)/*.idx $(TABLES)/*.toc $(TABLES)/*.out $(TABLES)/*~ $(TABLES)/*.nlo $(TABLES)/*.nls $(TABLES)/*.ist $(TABLES)/*.ilg
	rm -f $(APPENDICESDIR)/*.log $(APPENDICESDIR)/*.bak $(APPENDICESDIR)/*.aux $(APPENDICESDIR)/*.bbl $(APPENDICESDIR)/*.blg $(APPENDICESDIR)/*.idx $(APPENDICESDIR)/*.toc $(APPENDICESDIR)/*.out $(APPENDICESDIR)/*~ $(APPENDICESDIR)/*.nlo $(APPENDICESDIR)/*.nls $(APPENDICESDIR)/*.ist $(APPENDICESDIR)/*.ilg

# Clean all temporary resource files created during compilation and delete the latex output.
clean-all:
	rm -f *.dvi *.log *.bak *.aux *.bbl *.blg *.idx *.ps *.eps *.pdf *.toc *.out *~ *.lof *.lot *.nlo *.nls *.ist *.ilg
	rm -f $(CHAPTERSDIR)/*.dvi $(CHAPTERSDIR)/*.log $(CHAPTERSDIR)/*.bak $(CHAPTERSDIR)/*.aux $(CHAPTERSDIR)/*.bbl $(CHAPTERSDIR)/*.blg $(CHAPTERSDIR)/*.idx $(CHAPTERSDIR)/*.ps $(CHAPTERSDIR)/*.eps $(CHAPTERSDIR)/*.pdf $(CHAPTERSDIR)/*.toc $(CHAPTERSDIR)/*.out $(CHAPTERSDIR)/*~  $(CHAPTERSDIR)/*.nlo $(CHAPTERSDIR)/*.nls $(CHAPTERSDIR)/*.ist $(CHAPTERSDIR)/*.ilg
	rm -f $(TABLES)/*.dvi $(TABLES)/*.log $(TABLES)/*.bak $(TABLES)/*.aux $(TABLES)/*.bbl $(TABLES)/*.blg $(TABLES)/*.idx $(TABLES)/*.ps $(TABLES)/*.eps $(TABLES)/*.pdf $(TABLES)/*.toc $(TABLES)/*.out $(TABLES)/*~ $(TABLES)/*.nlo $(TABLES)/*.nls $(TABLES)/*.ist $(TABLES)/*.ilg
	rm -f $(APPENDICESDIR)/*.dvi $(APPENDICESDIR)/*.log $(APPENDICESDIR)/*.bak $(APPENDICESDIR)/*.aux $(APPENDICESDIR)/*.bbl $(APPENDICESDIR)/*.blg $(APPENDICESDIR)/*.idx $(APPENDICESDIR)/*.ps $(APPENDICESDIR)/*.eps $(APPENDICESDIR)/*.pdf $(APPENDICESDIR)/*.toc $(APPENDICESDIR)/*.out $(APPENDICESDIR)/*~ $(APPENDICESDIR)/*.nlo $(APPENDICESDIR)/*.nls $(APPENDICESDIR)/*.ist $(APPENDICESDIR)/*.ilg

# When using vim-latexsuite it adds annoying <++> symbols, this removes that shit from all .tex files
# by calling the predefined command above.
clean-eqs:
	$(CLEANEQS)
