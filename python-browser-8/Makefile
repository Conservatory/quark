CC=gcc
CFLAGS=-I.

all: .makeheader .tab_exec .tab_exec_2 .output_exec getcurpos

.makeheader: 
	./makeheader.sh

.%.o: %.c 
	$(CC) -c -o $@ $< $(CFLAGS)

.tab_exec_2_comp: tab_exec_2.o quarkexec.o
	$(CC) -o tab_exec_2 $^

.tab_exec_2: .tab_exec_2_comp
	sudo chown root tab_exec_2
	sudo chgrp quarkusers tab_exec_2
	sudo chmod 7750 tab_exec_2

.tab_exec_comp: tab_exec.o quarkexec.o
	$(CC) -o tab_exec $^

.tab_exec: .tab_exec_comp
	sudo chown root tab_exec
	sudo chgrp quarkusers tab_exec
	sudo chmod 7750 tab_exec


.output_exec_comp: output_exec.o quarkexec.o
	$(CC) -o output_exec $^

.output_exec: .output_exec_comp
	sudo chown root output_exec
	sudo chgrp quarkusers output_exec
	sudo chmod 7750 output_exec

getcurpos: getcurpos.c
	$(CC) -o getcurpos getcurpos.c -lX11

clean:
	rm *.h *.o tab_exec output_exec getcurpos

