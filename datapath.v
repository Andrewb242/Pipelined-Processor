`timescale 1ns / 1ps

module datapath(
    input clk
    );
 
    // Program Counter
    wire [31:0] pc, nextPc;
    wire stall;
    program_counter pcmodule(.clk(clk), .nextPc(nextPc), .pc(pc), .stall(stall));
    pc_adder pa(.pc(pc), .offset(32'd4), .nextPc(nextPc));
    
    // Instruction Memory
    wire [31:0] inst;
    inst_mem instmem(.pc(pc), .inst(inst));
    
    // IF/ID
    wire [31:0] inst_d;
    IF_ID_pipeline_reg IF_ID_pr(
        .clk(clk), .stall(stall),
        .inst(inst),
        .inst_d(inst_d)
    );
    
    /// Updated in MEM stage
    wire [31:0] writeData;
    wire [4:0] writeAddr_b;
    wire regWrite_b;
    
    /// Updated in current stage
    wire regWrite, memToReg, memWrite, aluSrc, regDst, memRead;
    
    // Register File
    wire [4:0] readAddr1 = inst_d[25:21];
    wire [4:0] readAddr2 = inst_d[20:16];
    wire [31:0] regOut1, regOut2;
    register_file regfile(.readAddr1(readAddr1), .readAddr2(readAddr2),
        .regOut1(regOut1), .regOut2(regOut2), .writeData(writeData),
        .writeAddr(writeAddr_b), 
        .regWrite(regWrite_b), .clk(clk)
    );

    // Control Unit
    wire [5:0] op = inst_d[31:26];
    wire [5:0] func = inst_d[5:0];
    wire [3:0] aluControl;
    control_unit cntr(.op(op), .func(func), .stall(stall),
    .regWrite(regWrite), .memToReg(memToReg), .memWrite(memWrite), .aluSrc(aluSrc), .regDst(regDst), .memRead(memRead), 
    .aluControl(aluControl)
    );
    
    // Sign Extend
    wire [15:0] imm16 = inst_d[15:0];
    wire [31:0] imm32;
    imm_extend imm_ext(.imm(imm16), .imm32(imm32));
    
    // rt, rd, rs
    wire [4:0] rt = inst_d[20:16];
    wire [4:0] rd = inst_d[15:11];
    wire [4:0] rs = inst_d[25:21];
    wire [4:0] rt_x;

    
    // Hazard Unit
    wire memRead_x;
    hazard_unit hazard_unt(
        .rt_x(rt_x), .rt_d(rt), .rs_d(rs),
        .memRead_x(memRead_x),
        .stall(stall)
    );
    
    // ID/EX
    wire regWrite_x, memToReg_x, memWrite_x, aluSrc_x, regDst_x;
    wire [31:0] regOut1_x, regOut2_x, imm32_x;
    wire [4:0] rd_x, rs_x;
    wire [3:0] aluControl_x;
    ID_EX_pipeline_reg ID_EX_pr(
        .clk(clk), .regWrite(regWrite), .memToReg(memToReg), .memWrite(memWrite), .aluSrc(aluSrc), .regDst(regDst), .memRead(memRead),
        .regOut1(regOut1), .regOut2(regOut2), .imm32(imm32),
        .rt(rt), .rd(rd), .rs(rs),
        .aluControl(aluControl),
        .regWrite_x(regWrite_x), .memToReg_x(memToReg_x), .memWrite_x(memWrite_x), .aluSrc_x(aluSrc_x), .regDst_x(regDst_x), .memRead_x(memRead_x),
        .regOut1_x(regOut1_x), .regOut2_x(regOut2_x), .imm32_x(imm32_x),
        .rt_x(rt_x), .rd_x(rd_x), .rs_x(rs_x),
        .aluControl_x(aluControl_x)
    );
    
    // Forwading Unit
    wire regWrite_m;
    wire [4:0] writeAddr_m;
    wire [1:0] forwardA, forwardB;
    forwarding_unit forwarding_unt(
        .writeAddr_m(writeAddr_m), .writeAddr_b(writeAddr_b), .rs_x(rs_x), .rt_x(rt_x),
        .regWrite_m(regWrite_m), .regWrite_b(regWrite_b),
        .forwardA(forwardA), .forwardB(forwardB)
    );
    
    // 3x1 Muxes
    wire [31:0] aluOut_m;
    wire [31:0] aluIn1;
    mux_3x1_32b muxA(
        .in0(regOut1_x), .in1(writeData), .in2(aluOut_m),
        .sel(forwardA),
        .out(aluIn1)
    );
    
    wire [31:0] muxBOut;
    mux_3x1_32b muxB(
        .in0(regOut2_x), .in1(writeData), .in2(aluOut_m),
        .sel(forwardB),
        .out(muxBOut)
    );
    
    // Alu 2x1 Multiplexer
    wire [31:0] aluIn2;
    mux_2x1_32b alu_mux(.in0(muxBOut), .in1(imm32_x), .sel(aluSrc_x), .out(aluIn2));
    
    // Alu
    wire [31:0] aluOut;
    alu alu(.aluIn1(aluIn1), .aluIn2(aluIn2), .aluOut(aluOut), .aluControl(aluControl_x));
    
    // Register Write Back Mux
    wire [4:0] writeAddr;
    mux_2x1_5b regWBAddrMux(.in0(rt_x), .in1(rd_x), .sel(regDst_x), .out(writeAddr));
    
    // EX/MEM
    wire memToReg_m, memWrite_m, memRead_m;
    wire [31:0] regOut2_m;
    EX_MEM_pipeline_reg EX_MEM_pr(
    .clk(clk), .regWrite_x(regWrite_x), .memToReg_x(memToReg_x), .memWrite_x(memWrite_x), .memRead_x(memRead_x),
    .aluOut(aluOut), .regOut2_x(muxBOut),
    .writeAddr(writeAddr),
    .regWrite_m(regWrite_m), .memToReg_m(memToReg_m), .memWrite_m(memWrite_m), .memRead_m(memRead_m),
    .aluOut_m(aluOut_m), .regOut2_m(regOut2_m),
    .writeAddr_m(writeAddr_m)
);
    
    // Data Memory
    wire [31:0] addr = aluOut_m;
    wire [31:0] memIn = regOut2_m;
    wire [31:0] memOut;
    data_mem data_mem(.addr(addr), .memIn(memIn), .memOut(memOut), .memWrite(memWrite_m), .memRead(memRead_m), .clk(clk));

    // MEM/WB
    wire memToReg_b;
    wire [31:0] aluOut_b, memOut_b;
    // wire [4:0] writeAddr_b; Declared above along with writeData
    MEM_WB_pipeline_reg MEM_WB_pr(
    .clk(clk), .regWrite_m(regWrite_m), .memToReg_m(memToReg_m),
    .aluOut_m(aluOut_m), .memOut(memOut),
    .writeAddr_m(writeAddr_m),
    .regWrite_b(regWrite_b), .memToReg_b(memToReg_b),
    .aluOut_b(aluOut_b), .memOut_b(memOut_b),
    .writeAddr_b(writeAddr_b)
);
    
    // WB Mux
    mux_2x1_32b writeBackMux(.in0(aluOut_b),.in1(memOut_b), .sel(memToReg_b), .out(writeData));
    
endmodule

/* ================= Modules to implement for HW1 =====================*/
module program_counter(
    input clk, stall,
    input [31:0] nextPc,
    output reg [31:0] pc
    );
    initial begin
        pc = 32'd96; // PC initialized to start from 100.
    end
    // ==================== Students fill here BEGIN ====================
    always @(posedge clk) begin
        if (!stall) begin
            pc <= nextPc;
        end
    end
    // ==================== Students fill here END ======================
endmodule

module pc_adder(
    input [31:0] pc, offset,
    output reg [31:0] nextPc
    );
    // ==================== Students fill here BEGIN ====================
    always @(pc) begin
        nextPc = pc + offset;
        // I used a blocking assignment because this circuit is combinational
    end
    // ==================== Students fill here END ======================
endmodule

/* ================= Modules to implement for HW3 =====================*/
module inst_mem(
    input [31:0] pc,
    output reg [31:0] inst
    );
    
    // This is an instruction memory that holds 64 instructions, 32b each.
    reg [31:0] memory [0:63];
    
    // Initializing instruction memory.
    initial begin       
        memory[25] = {6'b100011, 5'd0, 5'd1, 16'd0};
        memory[26] = {6'b100011, 5'd0, 5'd2, 16'd4};
        memory[27] = {6'b000000, 5'd1, 5'd2, 5'd3, 11'b00000100010};
        memory[28] = {6'b100011, 5'd3, 5'd4, 16'hFFFC};
        
        //memory[25] = {6'b100011, 5'd0, 5'd1, 16'd0};
        //memory[26] = {6'b100011, 5'd0, 5'd2, 16'd4};
        //memory[27] = {6'b100011, 5'd0, 5'd3, 16'd8};
        //memory[28] = {6'b100011, 5'd0, 5'd4, 16'd16};
        //memory[29] = {6'b000000, 5'd1, 5'd2, 5'd5, 11'b00000100000};
        //memory[30] = {6'b100011, 5'd3, 5'd6, 16'hFFFC};
        //memory[31] = {6'b000000, 5'd4, 5'd3, 5'd7, 11'b00000100010};
        
        //memory[25] = {6'b100011, 5'd0, 5'd1, 16'd0};
        //memory[26] = {6'b100011, 5'd0, 5'd2, 16'd4};
        //memory[27] = {6'b100011, 5'd0, 5'd4, 16'd16};
        //memory[28] = {6'b000000, 5'd1, 5'd2, 5'd3, 11'b00000100010};
        //memory[29] = {6'b100011, 5'd3, 5'd4, 16'hFFFC};
    end
    // ==================== Students fill here BEGIN ====================
    
    always @(*) begin
        inst = memory[pc[31:2]];
    end
    // ==================== Students fill here END ======================
endmodule

module register_file(
    input [4:0] readAddr1, readAddr2, writeAddr,
    input [31:0] writeData,
    input regWrite, clk,
    output reg [31:0] regOut1, regOut2
    );
    
    // Initializing registers. Do not touch here.
    reg [31:0] register [0:31]; // 32 registers, 32b each.
    integer i;
    initial begin
        for (i=0; i<32; i=i+1) begin
            register[i] = 32'd0; // Initialize to zero
        end
    end
    // ==================== Students fill here BEGIN ====================
    always @(negedge clk) begin
        if (regWrite == 1) begin
            register[writeAddr] <= writeData;
        end
    end
    
    always @(readAddr1, readAddr2, register) begin
        regOut1 = register[readAddr1];
        regOut2 = register[readAddr2];
    end

    // ==================== Students fill here END ======================
endmodule

module control_unit(
    input [5:0] op, func,
    input stall,
    output reg regWrite, memToReg, memWrite, aluSrc, regDst, memRead,
    output reg [3:0] aluControl
    );
    // ==================== Students fill here BEGIN ====================
    always @(*) begin
        // Set Default
        regWrite = 1'b0;
        memToReg = 1'b0;
        memWrite = 1'b0;
        aluSrc = 1'b0;
        regDst = 1'b0;
        memRead = 1'b0;
        aluControl = 4'b0000;
        if(!stall) begin
        if (op == 6'b000000) begin
            // R TYPE
            regWrite = 1;
            regDst = 1;
            case (func)
                6'b100000: aluControl = 4'b0010; // add
                6'b100010: aluControl = 4'b0110; // sub
            endcase
        end else if (op == 6'b100011) begin
            // LOAD
            regWrite = 1;
            aluSrc = 1;
            aluControl = 4'b0010;
            memRead = 1;
            memToReg = 1;
        end else if (op == 6'b101011) begin
            // STORE
            aluSrc = 1;
            memWrite = 1;
            aluControl = 4'b0010;
        end
        end
    end
    // ==================== Students fill here END ======================
endmodule

/* ================= Modules to implement for HW4 =====================*/
module imm_extend(
    input [15:0] imm,
    output reg [31:0] imm32
    );
    // ==================== Students fill here BEGIN ====================
    always @(*) begin
        imm32 = {{16{imm[15]}},imm[15:0]};
    end
    // ==================== Students fill here END ======================
endmodule

module mux_2x1_32b(
    input [31:0] in0, in1,
    input sel,
    output reg [31:0] out
    );
    // ==================== Students fill here BEGIN ====================
    always @(*) begin
        if (sel == 0) begin
            out = in0;
        end else if (sel == 1) begin
            out = in1;
        end
    end
    // ==================== Students fill here END ======================
endmodule

module alu(
    input [31:0] aluIn1, aluIn2,
    input [3:0] aluControl,
    output reg [31:0] aluOut
    );

    // ==================== Students fill here BEGIN ====================
    always @(*) begin
        case (aluControl)
            4'b0010: aluOut = aluIn1 + aluIn2;
            4'b0110: aluOut = aluIn1 - aluIn2;
            default: aluOut = 32'dx;
        endcase
    end
    // ==================== Students fill here END ======================
endmodule

module data_mem(
    input clk, memWrite, memRead,
    input [31:0] addr, memIn,
    output reg [31:0] memOut
    );
    
    reg [31:0] memory [0:63]; // 64x32 memory
    
    // Initialize data memory. Do not touch this part.
    initial begin
        memory[0] = 32'd16817;
        memory[1] = 32'd16801;
        memory[2] = 32'd16;
        memory[3] = 32'hDEAD_BEEF;
        memory[4] = 32'h4242_4242;
       
    end
    
    // ==================== Students fill here BEGIN ====================
    always @(memWrite, memRead, addr, memIn) begin
        if (memRead == 1) begin
            memOut = memory[addr[31:2]];
        end else begin
            memOut = 32'dx;
        end
    end
    
    always @(negedge clk) begin
        if (memWrite == 1) begin
            memory[addr[31:2]] <= memIn;
        end
    end
    // ==================== Students fill here END ======================
endmodule

/* ================= Modules to implement for HW5 =====================*/
module mux_2x1_5b(
    input [4:0] in0, in1,
    input sel,
    output reg [4:0] out
    );
    // ==================== Students fill here BEGIN ====================
    always @(*) begin
        if (sel == 0) begin
            out = in0;
        end else if (sel == 1) begin
            out = in1;
        end
    end
    // ==================== Students fill here END ======================
endmodule

// Begin Final Project

module IF_ID_pipeline_reg(
    input clk, stall,
    input [31:0] inst,
    output reg [31:0] inst_d
    );
    
    always @(posedge clk) begin
        if (!stall) begin
            inst_d <= inst;
        end
    end

endmodule

module ID_EX_pipeline_reg(
    input clk, regWrite, memToReg, memWrite, aluSrc, regDst, memRead,
    input [31:0] regOut1, regOut2, imm32,
    input [4:0] rt, rd, rs,
    input [3:0] aluControl,
    output reg regWrite_x, memToReg_x, memWrite_x, aluSrc_x, regDst_x, memRead_x,
    output reg [31:0] regOut1_x, regOut2_x, imm32_x,
    output reg [4:0] rt_x, rd_x, rs_x,
    output reg [3:0] aluControl_x
    );
    
    always @(posedge clk) begin
        regWrite_x <= regWrite;
        memToReg_x <= memToReg;
        memWrite_x <= memWrite;
        aluSrc_x <= aluSrc;
        regDst_x <= regDst;
        memRead_x <= memRead;
        regOut1_x <= regOut1;
        regOut2_x <= regOut2;
        imm32_x <= imm32;
        rt_x <= rt;
        rd_x <= rd;
        aluControl_x <= aluControl;
        rs_x <= rs;
    end
endmodule

module EX_MEM_pipeline_reg(
    input clk, regWrite_x, memToReg_x, memWrite_x, memRead_x,
    input [31:0] aluOut, regOut2_x,
    input [4:0] writeAddr,
    output reg regWrite_m, memToReg_m, memWrite_m, memRead_m,
    output reg [31:0] aluOut_m, regOut2_m,
    output reg [4:0] writeAddr_m
    );
    
    always @(posedge clk) begin
        regWrite_m <= regWrite_x;
        memToReg_m <= memToReg_x;
        memWrite_m <= memWrite_x;
        memRead_m <= memRead_x;
        aluOut_m <= aluOut;
        regOut2_m <= regOut2_x;
        writeAddr_m <= writeAddr;
    end
endmodule

module MEM_WB_pipeline_reg(
    input clk, regWrite_m, memToReg_m,
    input [31:0] aluOut_m, memOut,
    input [4:0] writeAddr_m,
    output reg regWrite_b, memToReg_b,
    output reg [31:0] aluOut_b, memOut_b,
    output reg [4:0] writeAddr_b
    );
    
    always @(posedge clk) begin
        regWrite_b <= regWrite_m;
        memToReg_b <= memToReg_m;
        aluOut_b <= aluOut_m;
        memOut_b <= memOut;
        writeAddr_b <= writeAddr_m;
    end
endmodule 

module forwarding_unit(
    input [4:0] writeAddr_m, writeAddr_b, rs_x, rt_x,
    input regWrite_m, regWrite_b,
    output reg [1:0] forwardA, forwardB
    );
    
    always @(*) begin
        forwardA = 0;
        forwardB = 0;
        if (regWrite_b == 1 && writeAddr_b != 0 && !(regWrite_m == 1 && writeAddr_m != 0 && writeAddr_m == rs_x) && writeAddr_b == rs_x) begin
                forwardA = 1;
            end
        if (regWrite_b == 1 && writeAddr_b != 0 && !(regWrite_m == 1 && writeAddr_m != 0 && writeAddr_m == rt_x) && writeAddr_b == rt_x) begin
                forwardB = 1;
        end
        if (regWrite_m == 1 && writeAddr_m != 0) begin
            if (writeAddr_m == rs_x) begin
                forwardA = 2;
            end
            if (writeAddr_m == rt_x) begin
                forwardB = 2;
            end
        end
    end
endmodule

module mux_3x1_32b(
    input [31:0] in0, in1, in2,
    input [1:0] sel,
    output reg [31:0] out
    );
    
    always @(*) begin
        if (sel == 0) begin
            out = in0;
        end else if (sel == 1) begin
            out = in1;
        end else if (sel == 2) begin
            out = in2;
        end
    end
endmodule

module hazard_unit(
    input [4:0] rt_x, rt_d, rs_d,
    input memRead_x,
    output reg stall
    );    
    always @(*) begin
        stall = 0;
        if (memRead_x == 1 && (rt_x == rs_d || rt_x == rt_d)) begin
            stall = 1;
        end
    end
    
    initial begin
        stall = 0;
    end

endmodule