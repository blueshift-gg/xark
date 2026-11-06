NVCC ?= nvcc
CUDA_TEST_BIN ?= /tmp/xark-msm-digits-test
BUCKET_TEST_BIN ?= /tmp/xark-msm-bucketize-test
HOST_TEST_BIN ?= /tmp/xark-msm-digits-host-test
BUCKET_HOST_TEST_BIN ?= /tmp/xark-msm-bucketize-host-test
FQ_HOST_TEST_BIN ?= /tmp/xark-msm-fq-host-probe
G1_HOST_TEST_BIN ?= /tmp/xark-msm-g1-host-probe
G1_CUDA_TEST_BIN ?= /tmp/xark-msm-g1-test
ACCUMULATE_HOST_TEST_BIN ?= /tmp/xark-msm-accumulate-host-probe
PLAN_HOST_TEST_BIN ?= /tmp/xark-msm-plan-host-test
INPUT_HOST_TEST_BIN ?= /tmp/xark-msm-input-host-probe
SCALAR_HOST_TEST_BIN ?= /tmp/xark-msm-scalar-host-probe
ACCUMULATE_CUDA_TEST_BIN ?= /tmp/xark-msm-accumulate-test
PIPELINE_CUDA_TEST_BIN ?= /tmp/xark-msm-pipeline-test
CXX ?= c++
NVCC_FLAGS ?= -std=c++17 -O3 -Xcompiler=-Wall,-Wextra,-Werror
CXX_FLAGS ?= -std=c++17 -O2 -Wall -Wextra -Werror

.PHONY: test test-host clean

test: test-host
	$(NVCC) $(NVCC_FLAGS) msm_digits_test.cu -o $(CUDA_TEST_BIN)
	$(CUDA_TEST_BIN)
	$(NVCC) $(NVCC_FLAGS) msm_bucketize_test.cu -o $(BUCKET_TEST_BIN)
	$(BUCKET_TEST_BIN)
	$(NVCC) $(NVCC_FLAGS) msm_g1_test.cu -o $(G1_CUDA_TEST_BIN)
	$(G1_CUDA_TEST_BIN)
	$(NVCC) $(NVCC_FLAGS) msm_accumulate_test.cu -o $(ACCUMULATE_CUDA_TEST_BIN)
	$(ACCUMULATE_CUDA_TEST_BIN)
	$(NVCC) $(NVCC_FLAGS) msm_pipeline_test.cu -o $(PIPELINE_CUDA_TEST_BIN)
	$(PIPELINE_CUDA_TEST_BIN)

test-host:
	$(CXX) $(CXX_FLAGS) msm_digits_host_test.cpp -o $(HOST_TEST_BIN)
	$(HOST_TEST_BIN)
	$(CXX) $(CXX_FLAGS) msm_bucketize_host_test.cpp -o $(BUCKET_HOST_TEST_BIN)
	$(BUCKET_HOST_TEST_BIN)
	$(CXX) $(CXX_FLAGS) msm_fq_host_probe.cpp -o $(FQ_HOST_TEST_BIN)
	python3 msm_fq_host_test.py $(FQ_HOST_TEST_BIN)
	$(CXX) $(CXX_FLAGS) msm_g1_host_probe.cpp -o $(G1_HOST_TEST_BIN)
	python3 msm_g1_host_test.py $(G1_HOST_TEST_BIN)
	$(CXX) $(CXX_FLAGS) msm_accumulate_host_probe.cpp -o $(ACCUMULATE_HOST_TEST_BIN)
	python3 msm_accumulate_host_test.py $(ACCUMULATE_HOST_TEST_BIN)
	$(CXX) $(CXX_FLAGS) msm_plan_host_test.cpp -o $(PLAN_HOST_TEST_BIN)
	$(PLAN_HOST_TEST_BIN)
	$(CXX) $(CXX_FLAGS) msm_input_host_probe.cpp -o $(INPUT_HOST_TEST_BIN)
	python3 msm_input_host_test.py $(INPUT_HOST_TEST_BIN)
	$(CXX) $(CXX_FLAGS) msm_scalar_host_probe.cpp -o $(SCALAR_HOST_TEST_BIN)
	python3 msm_scalar_host_test.py $(SCALAR_HOST_TEST_BIN)

clean:
	rm -f $(CUDA_TEST_BIN) $(BUCKET_TEST_BIN) $(G1_CUDA_TEST_BIN) \
	  $(ACCUMULATE_CUDA_TEST_BIN) $(PIPELINE_CUDA_TEST_BIN) $(HOST_TEST_BIN) \
	  $(BUCKET_HOST_TEST_BIN) $(FQ_HOST_TEST_BIN) $(G1_HOST_TEST_BIN) \
	  $(ACCUMULATE_HOST_TEST_BIN) $(PLAN_HOST_TEST_BIN) \
	  $(INPUT_HOST_TEST_BIN) $(SCALAR_HOST_TEST_BIN)
