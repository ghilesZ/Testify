SPLD=/usr/local/sicstus4.7.1/bin/spld
SICSTUS=/usr/local/sicstus4.7.1/bin/sicstus

all: oracle install

install: oracle
	mkdir -p ~/bin
	cp -f oracle ~/bin

oracle: prt.c oracle.c prt.sav
	@$(SPLD) --main=user --resources=prt.sav=/prt.sav prt.c oracle.c -o oracle

prt.sav: prt.pl
	@$(SICSTUS) --goal "compile(prt), save_program('prt.sav'), halt." --noinfo --nologo

clean:
	@rm -rf oracle prt.sav
