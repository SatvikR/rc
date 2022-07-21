# Builds examples

RCC=target/debug/rc
SRCS=$(wildcard examples/*.rc)
BINS=$(patsubst examples/%.rc, examples/%, $(SRCS))

all: $(BINS)

%: %.rc
	$(RCC) $^
clean:
	rm -f $(BINS)