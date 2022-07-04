RCC=../target/debug/rc
SRCS=$(wildcard *.rc)
BINS=$(patsubst %.rc, %, $(SRCS))

all: $(BINS)

%: %.rc
	$(RCC) $^
clean:
	rm -f $(BINS)