// `default_nettype none
`timescale 1ns/1ns

// MEMORY CONTROLLER
// > Receives memory requests from all cores
// > Throttles requests based on limited external memory bandwidth
// > Waits for responses from external memory and distributes them back to cores
module controller #(
    parameter ADDR_BITS = 8,
    parameter DATA_BITS = 16,
    parameter NUM_CONSUMERS = 4, // The number of consumers accessing memory through this controller
    parameter NUM_CHANNELS = 1,  // The number of concurrent channels available to send requests to global memory
    parameter WRITE_ENABLE = 1   // Whether this memory controller can write to memory (program memory is read-only)
) (
    input wire clk,
    input wire reset,

    // Consumer Interface (Fetchers / LSUs)
    mem_if.consumer consumer_if,
    // Memory Interface (Data / Program)
    mem_if.mem mem_if
);
    import states_pkg::*;

    // Keep track of state for each channel and which jobs each channel is handling
    controller_state_t controller_state [NUM_CHANNELS];
    logic [$clog2(NUM_CONSUMERS)-1:0] current_consumer [NUM_CHANNELS-1:0]; // Which consumer is each channel currently serving
    logic [NUM_CONSUMERS-1:0] channel_serving_consumer; // Which channels are being served? Prevents many workers from picking up the same request.

    always @(posedge clk) begin
        if (reset) begin 
            mem_if.read_valid <= 1'b0;
            mem_if.read_address <= '{default: '0};

            mem_if.write_valid <= 1'b0;
            mem_if.write_address <= '{default: '0};
            mem_if.write_data <= '{default: '0};

            consumer_if.read_ready <= 1'b0;
            consumer_if.read_data <= '{default: '0};
            consumer_if.write_ready <= 1'b0;

            current_consumer <= '{default: '0};
            controller_state <= CONTROLLER_IDLE;

            channel_serving_consumer <= '{default: '0};
        end else begin 
            // For each channel, we handle processing concurrently
            for (int i = 0; i < NUM_CHANNELS; i = i + 1) begin 
                case (controller_state_t'(controller_state[i]))
                    CONTROLLER_IDLE: begin
                        // While this channel is idle, cycle through consumers looking for one with a pending request
                        for (int j = 0; j < NUM_CONSUMERS; j = j + 1) begin 
                            if (consumer_if.read_valid[j] && !channel_serving_consumer[j]) begin 
                                channel_serving_consumer[j] = 1;
                                current_consumer[i] <= j;

                                mem_if.read_valid[i] <= 1;
                                mem_if.read_address[i] <= consumer_if.read_address[j];
                                controller_state[i] <= READ_WAITING;

                                // Once we find a pending request, pick it up with this channel and stop looking for requests
                                break;
                            end else if (consumer_if.write_valid[j] && !channel_serving_consumer[j]) begin 
                                channel_serving_consumer[j] = 1;
                                current_consumer[i] <= j;

                                mem_if.write_valid[i] <= 1;
                                mem_if.write_address[i] <= consumer_if.write_address[j];
                                mem_if.write_data[i] <= consumer_if.write_data[j];
                                controller_state[i] <= WRITE_WAITING;

                                // Once we find a pending request, pick it up with this channel and stop looking for requests
                                break;
                            end
                        end
                    end
                    READ_WAITING: begin
                        // Wait for response from memory for pending read request
                        if (mem_if.read_ready[i]) begin 
                            mem_if.read_valid[i] <= 0;
                            consumer_if.read_ready[current_consumer[i]] <= 1;
                            consumer_if.read_data[current_consumer[i]] <= mem_if.read_data[i];
                            controller_state[i] <= READ_RELAYING;
                        end
                    end
                    WRITE_WAITING: begin 
                        // Wait for response from memory for pending write request
                        if (mem_if.write_ready[i]) begin 
                            mem_if.write_valid[i] <= 0;
                            consumer_if.write_ready[current_consumer[i]] <= 1;
                            controller_state[i] <= WRITE_RELAYING;
                        end
                    end
                    // Wait until consumer acknowledges it received response, then reset
                    READ_RELAYING: begin
                        if (!consumer_if.read_valid[current_consumer[i]]) begin 
                            channel_serving_consumer[current_consumer[i]] = 0;
                            consumer_if.read_ready[current_consumer[i]] <= 0;
                            controller_state[i] <= CONTROLLER_IDLE;
                        end
                    end
                    WRITE_RELAYING: begin 
                        if (!consumer_if.write_valid[current_consumer[i]]) begin 
                            channel_serving_consumer[current_consumer[i]] = 0;
                            consumer_if.write_ready[current_consumer[i]] <= 0;
                            controller_state[i] <= CONTROLLER_IDLE;
                        end
                    end
                endcase
            end
        end
    end
endmodule
