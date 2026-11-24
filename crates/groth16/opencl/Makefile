CLANG ?= clang
CLANG_FLAGS ?= -x cl -cl-std=CL1.2 -Werror -Wno-poison-system-directories

.PHONY: test

test:
	tmp=$$(mktemp); trap 'rm -f "$$tmp"' EXIT; cat msm_pointwise.cl msm_digits.cl msm_bucket.cl > "$$tmp"; $(CLANG) $(CLANG_FLAGS) -fsyntax-only "$$tmp"
