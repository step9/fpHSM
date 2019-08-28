Program fpHSM;

{$Mode Delphi}
{$M+}

Uses
  classes,sysutils;
type 
  THSMStateData = 0..7;
  THSMStates = set of THSMStateData;
Const   
  HSM_EMPTY_SIG = 0;
  HSM_INIT_SIG = 1;
  HSM_ENTRY_SIG = 2;
  HSM_EXIT_SIG = 3;
  HSM_USER_SIG = 4;
  A_SIG = HSM_USER_SIG ;
  B_SIG = HSM_USER_SIG + 1;
  C_SIG = HSM_USER_SIG + 2;
  D_SIG = HSM_USER_SIG + 3;
  E_SIG = HSM_USER_SIG + 4;
  F_SIG = HSM_USER_SIG + 5;
  G_SIG = HSM_USER_SIG + 6;
  H_SIG = HSM_USER_SIG + 7;
  HSMStateCount = 13;
  //State defines
  HSM_Initial = 0;
  S_Top  = 1;
  S_0    = 2;
  S_1    = 3;
  S_1_1  = 4;
  S_2    = 5;
  S_2_1  = 6;
  S_2_1_1  = 7;
  StateDescs : Array [0..4] of string =
      ('State Inite','State Enter','State Leave','State State1','State State2');
  
Type 
   THSMMsg = Record
     msg:integer;
     data:Pointer;
   End;
   PHandler = ^THandler;
   PHSMState = ^THSMState;
   THandler = Function ( this:PHSMState;msg : THSMMsg):PHandler;
   
   THSMState = class
     private
       FsrcHandler,factHandler : PHandler;
       FActive : Integer;
     public
       //Property msgHandler : PHandler read FHandler;
       Procedure Start(st:PHandler);
       Procedure Init(st:PHandler);
       Procedure Trans(src,dst:PHandler);
       Function DispatchMsg(m : THSMMsg):Integer;
       Function HSM_Trigger(st:PHandler; msgid:Integer):PHandler;
   end;
   Function S0_Handler(this:PHSMState;msg : THSMMsg):PHandler; forward;
   Function S1_Handler(this:PHSMState;msg : THSMMsg):PHandler; forward;
   Function S2_Handler(this:PHSMState;msg : THSMMsg):PHandler; forward;
   Function S11_Handler(this:PHSMState;msg : THSMMsg):PHandler; forward;
   Function S21_Handler(this:PHSMState;msg : THSMMsg):PHandler; forward;
   Function S211_Handler(this:PHSMState;msg : THSMMsg):PHandler; forward;
   Function S_Top_Handler(this:PHSMState;msg : THSMMsg):PHandler; forward;
   Function HSM_Initial_Handler(this:PHSMState;msg : THSMMsg):PHandler; forward;
   
var
   StateArray : array [0..7] of THandler = (HSM_Initial_Handler,S_Top_Handler,S0_Handler,S1_Handler,S11_Handler,
                S2_Handler,S21_Handler,S211_Handler);

Var 
  tmpobj: THSMState; 
  hmsg : THSMMsg;
  bFoo : Boolean;
Function MakeMsg(msg:Integer):THSMMsg;
var
  m : THSMMsg;
begin
  m.msg := msg;
  Result := m;
end;
Function THSMState.HSM_Trigger(st:PHandler; msgid:Integer):PHandler;
begin
  Result := st^(@self,MakeMsg(msgid));
end;
Function THSMState.DispatchMsg(m : THSMMsg) : Integer ;
//var
//  tval : PHandler;
begin
//  tval := FactHandler^(@self,m);
//  while Integer(tval)<>0 do
//  begin
//    writeln('deep in hsm');
//    tval := tval^(@self,m);
//  end;
//  Result := 0;
  FsrcHandler := FactHandler;
  while assigned(FsrcHandler) do
     FsrcHandler := FsrcHandler^(@self,m);
     
end;
Procedure THSMState.Start(st:PHandler);
var
  s : pHandler;
begin 

    FactHandler := st ;
    FsrcHandler := @@StateArray[HSM_Initial];

    s := FactHandler;                               // save actState in a temporary
    FsrcHandler^(@self,MakeMsg(0));      // top-most initial tran.
                                    // initial transition must go one level deep

    s := FactHandler;                                     // update the temporary
    HSM_Trigger(s, HSM_ENTRY_SIG);           // enter the state
    while (PHandler(0) = HSM_Trigger(s, HSM_INIT_SIG)) do
    begin
        // init handled
        // initial transition must go one level deep
        s := FactHandler;
        HSM_Trigger(s, HSM_ENTRY_SIG);       // enter the substate
    end;
end;
Procedure THSMState.Init(st:PHandler);
begin
  FactHandler := st;
end;
Procedure THSMState.Trans(src,dst:PHandler);
label
  inLCA;
var
  entry : array [0..8] of PHandler;
  p, q, s : PHandler;
  e, lca: ^PHandler;
  t : PHandler;
begin
  s := FactHandler;
  while s <> FsrcHandler do
  begin        
    t := HSM_Trigger(s, HSM_EXIT_SIG);
    if assigned(t) then
       s := t // exit action unhandled, t points to superstate
    else  
      s := HSM_Trigger(s, HSM_EMPTY_SIG);// exit action handled, elicit superstate
     
  end;
  entry[0]:= PHandler(0);  
  e := @entry[0]; 
  inc(e);
  e^ := dst;  
    // (a) check source == target (transition to self)
  if (FsrcHandler = dst) then
  begin
    HSM_Trigger(FsrcHandler, HSM_EXIT_SIG);            // exit source
    goto inLCA;
  end;
    // (b) check source == dst->super
  p := HSM_Trigger(dst, HSM_EMPTY_SIG);
    if (FsrcHandler = p) then goto inLCA;
    //(c) check source->super == dst->super (most common)
  q := HSM_Trigger(FsrcHandler, HSM_EMPTY_SIG);
  if (q = p) then
  begin
    HSM_Trigger(FsrcHandler, HSM_EXIT_SIG);            // exit source
    goto inLCA;
  end;
    // (d) check source->super == dst
  if (q = dst) then
  begin
    HSM_Trigger(FsrcHandler, HSM_EXIT_SIG);           // exit source
    dec(e);                                     // not enter the LCA
    goto inLCA;
  end;
    // (e) check rest of source == dst->super->super... hierarchy
  inc(e);
  e^ := p; 
  s := HSM_Trigger(p, HSM_EMPTY_SIG);
  while assigned(s) do
  begin
    if (FsrcHandler = s) then 
       goto inLCA;
    inc(e);
    e^ := s; 
    s := HSM_Trigger(s, HSM_EMPTY_SIG);
  end;
  HSM_Trigger(FsrcHandler, HSM_EXIT_SIG);                // exit source
    // (f) check rest of source->super == target->super->super...
  lca := e;  
  while assigned(lca) do
  begin
    if (q = lca^) then
    begin
      e := lca;                      // do not enter the LCA
      dec(e);
      goto inLCA;
    end;
    dec(lca);
   end;
    // (g) check each srcState->super->super..for each target...
   s := q;
   while assigned(s) do
   begin
     lca := e;
     while assigned(lca^) do
     begin
       if (s = lca^) then
       begin
         e := lca ;  
	 dec(e);// do not enter the LCA
         goto inLCA;
       end;
       dec(lca);
     end;
      HSM_Trigger(s, HSM_EXIT_SIG);                        // exit s
      s := HSM_Trigger(s, HSM_EMPTY_SIG)
    end;                                          // malformed HSM
inLCA:         // now we are in the LCA of srcState and target
    s := e^;
    dec(e);
    while assigned(s) do
    begin
        // retrace the entry path in reverse order
        HSM_Trigger(s, HSM_ENTRY_SIG);                       // enter s
        s := e^;
        dec(e);
    end;
    FsrcHandler := dst;                   // update current state
    while (PHandler(0) = HSM_Trigger(dst, HSM_INIT_SIG)) do
    begin
        // initial transition must go one level deep
        //assert(target == Q_TRIGGER(actState, Q_EMPTY_SIG));
        dst := FactHandler;
        HSM_Trigger(dst, HSM_ENTRY_SIG);                // enter target
    end;
end;
Function HSM_Initial_Handler(this:PHSMState;msg : THSMMsg):PHandler;
begin
  writeln('HSM Initialised');
end;
Function S0_Handler(this:PHSMState;msg : THSMMsg):PHandler;  
begin
  writeln('S0_Handler ' + inttostr(msg.msg));
  if msg.msg > 0 then
  begin
    case msg.msg of 
      HSM_ENTRY_SIG:
      begin
        writeln('s0-ENTRY;');
        Result := PHandler(0);//该处可以作为整个状态机初始化的借口
	exit;
      end;
      HSM_EXIT_SIG:
      begin
        writeln('s0-EXIT;');
        Result := PHandler(0);
	exit;
      end;
      HSM_INIT_SIG:
      begin
        writeln('s0-INIT;');
        this^.Init(@@StateArray[S_1]);
        Result := PHandler(0);
	exit;
      end;
      E_SIG:
      begin
        writeln('s0-E;');
        this^.Trans(@@StateArray[S_0],@@StateArray[S_2_1_1]);
        Result := PHandler(0);
	exit;
      end;
   end;
   Result := @@StateArray[S_0];
  End;
  ////this^.trans(@@StateArray[0],@@StateArray[1]); 
  result := @@StateArray[S_Top];
end;


Function S1_Handler(this:PHSMState;msg : THSMMsg):PHandler; 
begin
  case msg.msg of 
    HSM_ENTRY_SIG:
      begin
        writeln('s1-ENTRY;'); 
        result := PHandler(0);
        exit;
      end;
    HSM_EXIT_SIG:
      begin
        writeln('s1-EXIT;'); 
        result := PHandler(0);
        exit;
      end;
    HSM_INIT_SIG:
      begin
        writeln('s1-INIT;'); 
        this^.Init(@@StateArray[S_1_1]);   
        result := PHandler(0);
        exit;
      end;
    A_SIG:
      begin
        writeln('s1-A;'); 
        This^.Trans(@@StateArray[S_1],@@StateArray[S_1]);  
        result := PHandler(0);
        exit;
      end;
    B_SIG:
      begin
        writeln('s1-B;'); 
        This^.Trans(@@StateArray[S_1],@@StateArray[S_1_1]);  
        result := PHandler(0);
        exit;
      end;
    C_SIG:
      begin
        writeln('s1-C;'); 
        This^.Trans(@@StateArray[S_1],@@StateArray[S_2]); 
        result := PHandler(0);
        exit;
      end;
    D_SIG:
      begin
        writeln('s1-D;'); 
        This^.Trans(@@StateArray[S_1],@@StateArray[S_0]); 
        result := PHandler(0);
        exit;
      end;
    F_SIG:
      begin
        writeln('s1-F;');
        This^.Trans(@@StateArray[S_1],@@StateArray[S_2_1_1]);
        result := PHandler(0);
        exit;
      end;
   end;
   Result := @@StateArray[S_0];
end;
Function S2_Handler(this:PHSMState;msg : THSMMsg):PHandler; 
begin
  case msg.msg of
    HSM_ENTRY_SIG: 
      begin
        writeln('s2-ENTRY;');
        result := PHandler(0);
        exit;
      end;
    HSM_EXIT_SIG: 
      begin
        writeln('s2-EXIT;');
        result := PHandler(0);
        exit;
      end;
    HSM_INIT_SIG: 
      begin
        writeln('s2-INIT;');
	This^.Init(@@StateArray[S_2_1]);
        result := PHandler(0);
        exit;
      end;
    C_SIG:     
      begin
        writeln('s2-C;');
        This^.Trans(@@StateArray[S_2],@@StateArray[S_1]);
        result := PHandler(0);
        exit;
      end;
    F_SIG:     
      begin
        writeln('s2-F;');
        This^.Trans(@@StateArray[S_2],@@StateArray[S_1_1]);
        result := PHandler(0);
        exit;
      end;
   end;
   Result := @@StateArray[S_0];
end;
Function S11_Handler(this:PHSMState;msg : THSMMsg):PHandler; 
Begin
  case msg.msg of
    HSM_ENTRY_SIG: 
      begin
        writeln('s11-ENTRY;');
        result := PHandler(0);
	exit;
      end;
    HSM_EXIT_SIG: 
      begin
        writeln('s11-EXIT;');
        result := PHandler(0);
	exit;
      end;
    G_SIG:  
      begin
        writeln('s11-G;');
	This^.Trans(@@StateArray[S_1_1],@@StateArray[S_2_1_1]);
        result := PHandler(0);
	exit;
      end;
    H_SIG:                 // internal transition with a guard
      begin
	 if (bFoo<>false) then
	 begin                     // test the guard condition
	   bFoo := false;
           writeln('s11-H;');
           result := PHandler(0);
	   exit;
	 end;       
      end;
   end;
   Result := @@StateArray[S_1];
End;
Function S21_Handler(this:PHSMState;msg : THSMMsg):PHandler; 
Begin
  case msg.msg of
    HSM_ENTRY_SIG: 
      begin
        writeln('s21-ENTRY;');
        result := PHandler(0);
	exit;
      end;
    HSM_EXIT_SIG: 
      begin
        writeln('s21-EXIT;');
        result := PHandler(0);
	exit;
      end;
    HSM_INIT_SIG:
      begin
        writeln('s21-INIT;');
	This^.Init(@@StateArray[S_2_1_1]);
        result := PHandler(0);
        exit;
      end;
    B_SIG:     
      begin
        writeln('s21-B;');
	This^.Trans(@@StateArray[S_2_1],@@StateArray[S_2_1_1]);
        result := PHandler(0);
	exit;
      end;
    H_SIG:                     // self transition with a guard
      begin
        if (not bFoo) then
        begin           // test the guard condition
          writeln('s21-H;');
          bFoo := true;
          This^.Trans(@@StateArray[S_2_1],@@StateArray[S_2_1]);                   // self transition
          result := PHandler(0);
	  exit;
        end;
      end; 
   end;
   Result := @@StateArray[S_2];
End;
Function S211_Handler(this:PHSMState;msg : THSMMsg):PHandler;
Begin
  case msg.msg of
    HSM_ENTRY_SIG: 
      begin
        writeln('s211-ENTRY;');
        result := PHandler(0);
	exit;
      end;
    HSM_EXIT_SIG: 
      begin
        writeln('s211-EXIT;');
        result := PHandler(0);
	exit;
      end;
    D_SIG: 
      begin
        writeln('s211-D;');
	This^.Trans(@@StateArray[S_2_1_1],@@StateArray[S_2_1]);
        result := PHandler(0);
	exit;
      end;
    G_SIG: 
      begin
        writeln('s211-G;');
	This^.Trans(@@StateArray[S_2_1_1],@@StateArray[S_0]);
        result := PHandler(0);
	exit;
      end;
   end;
   Result := @@StateArray[S_2_1];
End;
Function S_Top_Handler(this:PHSMState;msg : THSMMsg):PHandler; 
Begin
  result := PHandler(0);
End;
var
  rslt : Integer;
  c : char;
begin
  //asm int 3 end;
  tmpobj := THSMState.Create;
  tmpobj.Start(@@StateArray[S_0]);
  //asm int 3 end;
  hmsg.msg := 12;
  //asm int 3 end;
  //rslt := tmpObj.DispatchMsg(hmsg);
  //asm int 3 end;
  //rslt := tmpObj.DispatchMsg(hmsg);
  //rslt := tmpObj.DispatchMsg(hmsg);
  Writeln ('Hiberarchy state machine testing');   
  while (1=1) do
    begin
      writeln('Signal<-');
      readln(c); 
      if (ord(c) < ord('a')) or (ord('h') < ord(c)) then
      begin
        exit;
      end;
      hmsg.msg := ord(c) - ord('a')+ HSM_USER_SIG;
      tmpObj.DispatchMsg(hmsg); // dispatch
    end;
    //Result := 0;
end.
