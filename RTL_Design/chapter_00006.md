# Pipelining and Parallelism

## Basics of Pipelining
Pipelining is a technique where multiple instruction phases are overlapped to improve performance.

### Example: 2-Stage Pipeline
```SV
module pipeline_stage (
    input logic clk,
    input logic reset,
    input logic [3:0] in,
    output logic [3:0] out
);
    logic [3:0] stage1, stage2;

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            stage1 <= 4'b0000;
            stage2 <= 4'b0000;
        end else begin
            stage1 <= in;
            stage2 <= stage1;
        end
    end

    assign out = stage2;
endmodule
```

## Implementing Pipeline Stages
Pipeline stages are implemented by breaking down a process into smaller stages, each handled by a separate pipeline stage.

## Handling Data Hazards
Data hazards occur when pipeline stages depend on the results of previous stages. Techniques like forwarding and stalling are used to handle these hazards.

### Example: Data Hazard Handling
```SV
module hazard_handling (
    input logic clk,
    input logic reset,
    input logic [3:0] in,
    output logic [3:0] out
);
    logic [3:0] stage1, stage2, stage3;

    always_ff @(posedge clk or posedge reset) begin
        if (reset) begin
            stage1 <= 4'b0000;
            stage2 <= 4'b0000;
            stage3 <= 4'b0000;
        end else begin
            stage1 <= in;
            stage2 <= stage1;
            stage3 <= stage2;
        end
    end

    assign out = stage3;
endmodule
```

## Exercises

1. Design a 3-stage pipeline for a simple arithmetic operation.
2. Implement a pipeline with data forwarding to handle hazards.
3. Write a SystemVerilog module to demonstrate stalling in a pipeline.
