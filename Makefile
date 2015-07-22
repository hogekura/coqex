DIRS := 1 2 3 4 5 6 7 8 9

all : $(DIRS)
$(DIRS):
	make -C $@

clean:
	for i in $(DIRS); do make -C ./$$i clean; done
