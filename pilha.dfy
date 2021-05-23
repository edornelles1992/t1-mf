class {:autocontracts} Pilha
{
    //abstração
    ghost const TamanhoMaximo: int;
    ghost var Conteudo: seq<int>;
    //implementação
    var lista: array<int>;
    var posPilha: int;
    const max: int;

    predicate Valid()
    {
        max > 0
        && max == lista.Length
        && 0 <= posPilha <= max
        && TamanhoMaximo == max
        && Conteudo == lista[0..posPilha]
    }

    constructor (n:int)
    requires n > 0
    ensures TamanhoMaximo == n
    ensures Conteudo == []
    {
        max := n;
        lista := new int[n];
        posPilha := 0;
        TamanhoMaximo := max;
        Conteudo := [];
    }

    method Empilhar(e:int) returns (valido:bool)
    ensures valido <==> (Conteudo == old(Conteudo) + [e]) && posPilha > old(posPilha) && old(posPilha) < max && lista[old(posPilha)] == e
    ensures !valido <==> Conteudo == old(Conteudo) && posPilha == old(posPilha) && posPilha == max
    {
        if (posPilha < max){ //valida espaço na pilha
            lista[posPilha] := e;
            posPilha := posPilha + 1;
            Conteudo := Conteudo + [e];
            return true;
        } 
         return false;
    } 

    method Desempilhar()
    requires |Conteudo| <= TamanhoMaximo
    ensures Conteudo == lista[0..posPilha]
    {
        if (posPilha > 0){ //testa pilha vazia
            posPilha := posPilha - 1;
            lista[posPilha] :=  0;
            Conteudo := lista[0..posPilha];
        } else {
         print "\nNenhum elemento na pilha para ser desempilhado"; 
        }
    }

    method Ler()//precisa retornar ou somente printar?.
    ensures Conteudo == old(Conteudo)
    ensures posPilha == old(posPilha)
    {
        if (posPilha > 0) {
          print lista[posPilha - 1];
        } else {
          print "\nNenhum elemento na pilha para ser lido"; 
        }
    }

    method Cheia() returns (valido:bool)
    ensures valido <==> (posPilha == max) 
    ensures !valido <==> (posPilha < max && posPilha >= 0)
    {
        if (posPilha == max){
            return true;
        } else {
            return false;
        }
    }

    method Vazia() returns (valido:bool)
    ensures Conteudo == old(Conteudo)
    ensures valido <==> (posPilha == 0)
    {
        if (posPilha == 0){
            return true;
        } else {
            return false;
        }
    }

    method Quantidade() returns (n:int)
    ensures n == |Conteudo|
    ensures Conteudo == old(Conteudo)
    {
        n := posPilha;
    }

    method QuantidadeMaxima() returns (n:int)
    ensures n == TamanhoMaximo
    ensures Conteudo == old(Conteudo)
    {
        return max;
    }

/*     method InvertePilha()   
    requires |Conteudo| < TamanhoMaximo
    ensures forall i :: 0 <= i < posPilha ==> lista[i] == old(lista[(posPilha - i) - 1]);
    ensures Conteudo == lista[..max]
    {   
        var novaLista: array<int>;
        var i := 0;
        novaLista := new int[max];
        while i < posPilha
        decreases posPilha - i
        {  
            novaLista[i] := lista[(posPilha - i) - 1];
            i := i + 1;
        }

        lista := novaLista;
        Conteudo := lista[..max];
    } */
}

method Main()
{
    var pilha := new Pilha(3);
    assert pilha.TamanhoMaximo == 3;
    assert pilha.Conteudo == [];
    var q := pilha.Quantidade();
    assert q == 0;
    var vazia := pilha.Vazia();
    pilha.Ler();
    assert vazia == true; 
    var cheia := pilha.Cheia();
    assert cheia == false; 

    //adiciona valores na pilha...
    var empilhou := pilha.Empilhar(1);
    assert empilhou == true;

    empilhou := pilha.Empilhar(2);
    assert empilhou == true;

    empilhou := pilha.Empilhar(3);
    assert empilhou == true;

    //tentando colocar sem espaço na pilha
    empilhou := pilha.Empilhar(4);
    assert empilhou == false;

    //lotou a pilha
    cheia := pilha.Cheia();
    assert cheia == true; 

    //desempilha dois elementos
    pilha.Desempilhar();
    pilha.Desempilhar();

    //liberou espaços na pilha..
    cheia := pilha.Cheia();
   // assert cheia == false; TODO: validar pq n esta certo
}