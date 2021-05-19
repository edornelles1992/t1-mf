class {:autocontracts} Pilha
{
    ghost const TamanhoMaximo: nat;
    ghost var Conteudo: seq<nat>;
    var lista: array<nat>;
    var tail: nat;
    const max: nat;

    predicate Valid()
    {
        max > 0
        && max == lista.Length
        && 0 <= tail <= max
        && TamanhoMaximo == max
        && Conteudo == lista[0..tail]
    }

    constructor (n:nat)
    requires n > 0
    ensures TamanhoMaximo == n
    ensures Conteudo == []
    {
        max := n;
        lista := new nat[n];
        tail := 0;
        TamanhoMaximo := max;
        Conteudo := [];
    }

     method Empilhar(e:nat) returns (valido:bool)

     method Desempilhar()

     method Ler() returns (n:nat) //precisa retornar ou somente printar?.

     method Cheia() returns (valido:bool)

     method Vazia() returns (valido:bool)

    method Quantidade() returns (n:nat)
    ensures n == |Conteudo|
    ensures Conteudo == old(Conteudo)
    {
        n := tail;
    }

    method QuantidadeMaxima() returns (n:nat)
    ensures n == TamanhoMaximo
    ensures Conteudo == old(Conteudo)
    {
        return max;
    }

     method InvertePilha() 
}

method Main()
{
    var pilha := new Pilha(5);
    assert pilha.TamanhoMaximo == 5;
    assert pilha.Conteudo == [];
 //   var q := pilha.Quantidade();
 //   assert q == 0;
}