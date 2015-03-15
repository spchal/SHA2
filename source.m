# SHA2
input := "616263";

k:=[0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2];

Preprocess:=function(input)
	paddedMessage := [];

	for i in [1..#input/2] do
	    paddedMessage := paddedMessage cat [StringToInteger(input[i*2-1..i*2], 16)];
	end for;

	k := "1";
	for i in [1..(448 - #input*4 - 1) mod 512] do
	    k:=k cat "0";
	    if #k eq 8 then
	        paddedMessage := paddedMessage cat [StringToInteger(k, 2)];
	        k := "";
	    end if;
	end for;

	if k ne "" then
	    paddedMessage := paddedMessage cat [StringToInteger(k, 2)];
	end if;

	tempPadding := [];
	k := "";
	for i in Intseq(#input*4,2) do
	    k := IntegerToString(i) cat k;
	    if #k eq 8 then
	        tempPadding := tempPadding cat [StringToInteger(k, 2)];
	        k := "";
	    end if;
	end for;

	bitCount := #Intseq(#input*4, 2);
	for i in [1..64-bitCount] do
	    k := "0" cat k;
	    if #k eq 8 then
	        tempPadding := [StringToInteger(k, 2)] cat tempPadding;
	        k := "";
	    end if;
	end for;

	paddedMessage := paddedMessage cat tempPadding;

	return paddedMessage;
end function;

RotateInt := function(intNum, bits)
    return BitwiseOr(ShiftRight(intNum, bits), ShiftLeft(intNum, 32 - bits));
end function;

stringPad:=function(str)
	hex:= Eltseq(IntegerToString(str,16));
	while #hex lt 8 do
		hex:=Insert(hex,1,"0");
	end while;
	a:="";
	for i in [1..#hex]do
		a cat:=hex[i];
	end for;
	return a;
end function;

processMessage := function(msgSchedule)
    msgBlocks := [];
    for i in [1..#msgSchedule] do
        partitions := Partition(msgSchedule[i], 4);
       // partitions;
        block := [];
        for j in partitions do
            temp := 0;
            for k in [1..#j] do
                temp := ShiftLeft(temp, 8) + j[k];
				//printf "temp: ";temp:Hex;
            end for;
            block := block cat [temp];
        end for;
        msgBlocks := msgBlocks cat [block];
    end for;
    //msgBlocks;

    h0 := 0x6a09e667;
    h1 := 0xbb67ae85;
    h2 := 0x3c6ef372;
    h3 := 0xa54ff53a;
    h4 := 0x510e527f;
    h5 := 0x9b05688c;
    h6 := 0x1f83d9ab;
    h7 := 0x5be0cd19;

    word64 := [];
    for i in [1..#msgBlocks] do
        word64 := msgBlocks[i];
        

        for i in [17..64] do
            s0 := BitwiseXor(RotateInt(word64[i - 15], 7), RotateInt(word64[i - 15], 18));
            s0 := BitwiseXor(s0, ShiftRight(word64[i-15], 3));

            s1 := BitwiseXor(RotateInt(word64[i-2],17),RotateInt(word64[i-2],19));
            s1 := BitwiseXor(s1, ShiftRight(word64[i-2],10));

            word64[i]:= (word64[i-16] + s0 + word64[i-7] + s1) mod 2^32;
        end for;

        //Initialize working variables to current hash value:
        a := h0;
        b := h1;
        c := h2;
        d := h3;
        e := h4;
        f := h5;
        g := h6;
        h := h7;

        //Compression function main loop:
        for i in [1..64]do
            s1 := BitwiseXor(BitwiseXor(RotateInt(e, 6), RotateInt(e,11)), RotateInt(e,25));

            not_e := BitwiseNot(e);
            ch:= BitwiseXor(BitwiseAnd(e, f), BitwiseAnd(not_e, g));

            //ki:=HexToBinarySequence(k[i]);
            temp1 := (h + s1 + ch + k[i] + word64[i])mod 2^32;
            //temp1:=addWords(addWords(addWords(h,s1),addWords(ch,ki)),word64[i]);

            //s0:=xorWords(xorWords(Rotate(a,2),Rotate(a,13)),Rotate(a,22));
            s0:= BitwiseXor(BitwiseXor(RotateInt(a, 2), RotateInt(a, 13)), RotateInt(a, 22));

            //x1:=xorWords(andWords(a,b),andWords(a,c));
            x1 := BitwiseXor(BitwiseAnd(a, b), BitwiseAnd(a, c));
            //maj:=xorWords(x1,andWords(b,c));
            maj := BitwiseXor(x1, BitwiseAnd(b, c));
            //temp2:=addWords(s0,maj);
            temp2 := (s0 + maj)mod 2^32;

            h := g;
            g := f;
            f := e;
            e := (d + temp1)mod 2^32;
            d := c;
            c := b;
            b := a;
            a := (temp1 + temp2)mod 2^32;
			//i;printf "a: "; a:Hex;
        end for;
        //Add the compressed chunk to the current hash value

        h0:= (h0 + a) mod 2^32;
        h1:= (h1 + b) mod 2^32;
        h2:= (h2 + c) mod 2^32;
        h3:= (h3 + d) mod 2^32;
        h4:= (h4 + e) mod 2^32;
        h5:= (h5 + f) mod 2^32;
        h6:= (h6 + g) mod 2^32;
        h7:= (h7 + h) mod 2^32;

    end for;
	//printf"h0:";h0:Hex;
	
    digest:= stringPad(h0) cat stringPad(h1) cat stringPad(h2) cat stringPad(h3) cat stringPad(h4) cat stringPad(h5) cat stringPad(h6) cat stringPad(h7);
    return digest;
end function;


hashSHA2:= function(input)
	paddedMsg := Preprocess(input);
	messageSchedule := Partition(paddedMsg, 64);
	out:=processMessage(messageSchedule);
	return out;
end function;

//TESTING
//hashSHA2("6162636462636465636465666465666765666768666768696768696A68696A6B696A6B6C6A6B6C6D6B6C6D6E6C6D6E6F6D6E6F706E6F7071");
tvSHA2 := 
  [
  [* // test vector 1
  // input
  "616263",
  // output
  "BA7816BF8F01CFEA414140DE5DAE2223B00361A396177A9CB410FF61F20015AD"
  *],
  [* // test vector 2
  // input
  "6162636462636465636465666465666765666768666768696768696A68696A6B696A6B6C6A6B6C6D6B6C6D6E6C6D6E6F6D6E6F706E6F7071",
  // output
  "248D6A61D20638B8E5C026930C3E6039A33CE45964FF2167F6ECEDD419DB06C1"
  *],
  [* // test vector 3
  // input
  "616D6272612065206769756C69612068616E6E6F20636F6D706C657461746F206C27696\
D706C656D656E74617A696F6E65206469205348412D3235362E2046756E7A696F6E612062656E6\
521",
  // output
  "C17B7A1F3B6A5191B2946E2C03146860AB37758F2A3EE3B3D17A158053187E9D"
  *],
  [* // test vector 4
  // input
  "63727970746F677261706879",
  // output
  "E06554818E902B4BA339F066967C0000DA3FCDA4FD7EB4EF89C124FA78BDA419"
  *]
  ];



procedure testSHA2(hashSHA2,tvSHA2)

  alltest := true;
  for i in [1..#tvSHA2] do
    print "testing test vector #",i;
    tv := tvSHA2[i];
    a := hashSHA2(tv[1]);
    thistest := (a eq tv[2]);
    print "  test passed = ", thistest;
    alltest := thistest and alltest;
  end for;
  print"All test passed? ", alltest;
  
end procedure;

function timeSHA2(hashSHA2,tvSHA2)
  
  t := Cputime();

  for i in [1..100] do
    j := (i mod #tvSHA2) + 1;
    tv := tvSHA2[j];
    a := hashSHA2(tv[1]);
  end for;
  
  return Cputime(t);
  
end function;
 testSHA2(hashSHA2,tvSHA2);
 timeSHA2(hashSHA2,tvSHA2);
