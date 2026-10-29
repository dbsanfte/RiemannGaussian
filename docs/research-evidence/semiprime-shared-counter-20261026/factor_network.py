#!/usr/bin/env python3
"""Exact macro-FFT Boolean tensor compiler, standard library only.
No contraction algorithm or factoring oracle is implemented. compile(N) returns
ordered bit ports, edges, local 0/1 entry predicates and a witness validator.
"""
from dataclasses import dataclass, replace
from pathlib import Path
import argparse
import json


def bits(value, width):
    return tuple((value >> i) & 1 for i in range(width))


def unpack(data, widths):
    out=[];offset=0
    for width in widths:
        out.append(sum(data[offset+i] << i for i in range(width)))
        offset+=width
    return out


def dft(values, root, modulus, normalizer=1):
    out=[]
    for k in range(len(values)):
        ratio=pow(root,k,modulus);power=1;acc=0
        for value in values:
            acc=(acc+value*power)%modulus
            power=power*ratio%modulus
        out.append(acc*normalizer%modulus)
    return out


@dataclass(frozen=True)
class Vertex:
    kind: str
    ports: tuple
    widths: tuple
    inputs: int
    params: dict
    side: int = 0
    restrictions: tuple = ()

    def entry(self, data):
        """Evaluate one local tensor entry; never emit its truth table."""
        if len(data)!=len(self.ports) or any(x not in (0,1) for x in data):
            return 0
        if any(data[pos]!=value for pos,value in self.restrictions):
            return 0
        values=unpack(data,self.widths)
        ins,outs=values[:self.inputs],values[self.inputs:]
        p=self.params;k=self.kind
        if k=='equality':return int(data[0]==data[1])
        if k=='digit':
            word,flag=outs
            wanted=(word>=2) if p['index']==0 else (word!=0)
            return int(word<(1<<p['digit_bits']) and flag==wanted)
        if k=='const':return int(outs==[p['value']])
        if k=='one_check':return int(ins==[1])
        if k=='zero_check':return int(ins==[0])
        if k=='or':return int(outs==[int(bool(ins[0] or ins[1]))])
        if k=='carry':
            coefficient,carry=ins;next_carry=outs[0]
            return int(coefficient<p['modulus'] and carry<(1<<p['n'])
                       and next_carry<(1<<p['n'])
                       and coefficient+carry==p['digit']+(1<<p['b'])*next_carry)
        modulus=p['modulus']
        if any(x>=modulus for x in values):return 0
        if k=='dft':expected=dft(ins,p['root'],modulus,p['normalizer'])
        elif k=='scale':expected=[ins[0]*p['coefficient']%modulus]
        elif k=='multiply':expected=[ins[0]*ins[1]%modulus]
        else:raise AssertionError(k)
        return int(outs==expected)


@dataclass(frozen=True)
class Edge:
    ends: tuple  # ((vertex_id, ordered_port_index), (vertex_id, ordered_port_index))


@dataclass(frozen=True)
class Step:
    vertex: int
    input_words: tuple
    output_words: tuple


class Builder:
    def __init__(self):
        self.vertices=[];self.ends=[];self.steps=[]

    def add(self,kind,inputs,out_widths,params):
        vid=len(self.vertices)
        in_ports=tuple(e for word in inputs for e in word)
        for pos,e in enumerate(in_ports):
            assert len(self.ends[e])==1,'signal must have one consumer'
            self.ends[e].append((vid,pos))
        outputs=[];ports=list(in_ports)
        for width in out_widths:
            word=[]
            for _ in range(width):
                e=len(self.ends);self.ends.append([(vid,len(ports))])
                ports.append(e);word.append(e)
            outputs.append(tuple(word))
        widths=tuple(len(word) for word in inputs)+tuple(out_widths)
        self.vertices.append(Vertex(kind,tuple(ports),widths,len(inputs),dict(params)))
        self.steps.append(Step(vid,tuple(inputs),tuple(outputs)))
        return outputs


class Network:
    def __init__(self,N,parameters,vertices,edges,steps,original_vertices,input_bits,hosts):
        self.N=N;self.parameters=parameters
        self.vertices=tuple(vertices);self.edges=tuple(edges);self.steps=tuple(steps)
        self.original_vertices=tuple(original_vertices)
        self.input_bits={key:tuple(value) for key,value in input_bits.items()}
        self.hosts=tuple(hosts)

    def validate(self,assignment):
        if len(assignment)!=len(self.edges):return {'valid':False,'failed_vertices':['assignment_length']}
        failed=[i for i,v in enumerate(self.vertices)
                if not v.entry(tuple(assignment[e] for e in v.ports))]
        return {'valid':not failed,'failed_vertices':failed}

    def restrict(self,fixed):
        """Restrict actual bit edges inside existing predicates, no extra ports."""
        vertices=list(self.vertices)
        for edge,value in fixed.items():
            if not 0<=edge<len(self.edges) or value not in (0,1):raise ValueError('invalid restriction')
            vid,pos=self.hosts[edge]
            vertices[vid]=replace(vertices[vid],restrictions=vertices[vid].restrictions+((pos,value),))
        return Network(self.N,self.parameters,vertices,self.edges,self.steps,
                       self.original_vertices,self.input_bits,self.hosts)

    def witness(self,P,Q):
        """Fill every bit edge from supplied integers, then check ALL predicates.
        Invalid/out-of-range supplied values force a malformed digit, rather than
        silently validating their truncation. This is a verifier, not a factorer.
        """
        par=self.parameters;n=par['nfft'];mod=par['modulus'];L=par['L'];base=1<<par['b']
        original=[0]*(len(self.edges)//2)
        operands={'P':P,'Q':Q}
        for step in self.steps:
            v=self.original_vertices[step.vertex];p=v.params;k=v.kind
            ins=[sum(original[e]<<i for i,e in enumerate(word)) for word in step.input_words]
            if k=='digit':
                operand=operands[p['operand']]
                word=(operand>>(par['b']*p['index']))&(base-1) if operand>=0 else 0
                if not 0<=operand<(1<<L) and p['index']==0:word=mod
                flag=int(word>=2) if p['index']==0 else int(word!=0)
                outs=[word,flag]
            elif k=='const':outs=[p['value']]
            elif k in ('one_check','zero_check'):outs=[]
            elif k=='or':outs=[int(bool(ins[0] or ins[1]))]
            elif k=='carry':outs=[(ins[0]+ins[1])//base]
            elif k=='dft':outs=dft(ins,p['root'],mod,p['normalizer'])
            elif k=='scale':outs=[ins[0]*p['coefficient']%mod]
            elif k=='multiply':outs=[ins[0]*ins[1]%mod]
            else:raise AssertionError(k)
            assert len(outs)==len(step.output_words)
            for word,value in zip(step.output_words,outs):
                for i,e in enumerate(word):original[e]=(value>>i)&1
        assignment=tuple(value for bit in original for value in (bit,bit))
        result=self.validate(assignment)
        result.update(P=P,Q=Q,assignment=assignment)
        return result

    def descriptor(self):
        """Finite port/parameter description, excluding exponential truth tables."""
        return dict(N=self.N,parameters=self.parameters,input_bits=self.input_bits,
                    vertices=[dict(kind=v.kind,ports=v.ports,widths=v.widths,inputs=v.inputs,
                                   params=v.params,side=v.side,restrictions=v.restrictions)
                              for v in self.vertices],
                    edges=[edge.ends for edge in self.edges])

    def statistics(self):
        L=self.parameters['L'];n=self.parameters['nfft'];degree=max((len(v.ports) for v in self.vertices),default=0)
        return dict(N=self.N,L=L,nfft=n,word_bits=n+1,digit_bits=self.parameters['b'],
                    digits=self.parameters['d'],vertices=len(self.vertices),edges=len(self.edges),
                    maximum_degree=degree,total_ports=sum(len(v.ports) for v in self.vertices),
                    edges_le_100_nfft_squared=len(self.edges)<=100*n*n,
                    edges_le_6400_L=len(self.edges)<=6400*L,
                    degree_fourth_power_bound=degree**4<=100**4*L**3,
                    D1_s=1024*L,D1_degree_bound=degree**10<=(1024*L)**9,
                    counting_precision=2*L+1,
                    not_implemented=['tensor contraction','D1 algorithm','factoring search'])


def compile(N):
    if not isinstance(N,int) or N<2:raise ValueError('N must be an integer at least 2')
    L=N.bit_length();n=4
    while n*n<16*L:n*=2
    b=n//4;d=(L+b-1)//b;modulus=(1<<n)+1;width=n+1
    assert d<=n//4 and d*((1<<b)-1)**2<1<<n
    omega=4;assert pow(omega,n//2,modulus)==modulus-1
    r=1<<((n.bit_length()-1)//2);t=n//r
    G=Builder();input_original={'P':[],'Q':[]}

    def make_input(operand):
        words=[];flags=[]
        for i in range(n):
            if i<d:
                digit_bits=min(b,L-i*b)
                word,flag=G.add('digit',[],[width,1],dict(operand=operand,index=i,digit_bits=digit_bits))
                words.append(word);flags.append(flag)
                input_original[operand].extend(word[:digit_bits])
            else:words.append(G.add('const',[],[width],dict(value=0))[0])
        flag=flags[0]
        for other in flags[1:]:flag=G.add('or',[flag,other],[1],{})[0]
        G.add('one_check',[flag],[],{})
        return words

    def transform(words,inverse=False):
        root=pow(omega,-1,modulus) if inverse else omega
        a={}
        for j1 in range(r):
            out=G.add('dft',[words[j1+r*j2] for j2 in range(t)],[width]*t,
                      dict(root=pow(root,r,modulus),modulus=modulus,normalizer=1))
            for k2 in range(t):a[j1,k2]=out[k2]
        scaled={}
        for j1 in range(r):
            for k2 in range(t):
                scaled[j1,k2]=G.add('scale',[a[j1,k2]],[width],
                    dict(coefficient=pow(root,j1*k2,modulus),modulus=modulus))[0]
        result=[None]*n
        for k2 in range(t):
            out=G.add('dft',[scaled[j1,k2] for j1 in range(r)],[width]*r,
                      dict(root=pow(root,t,modulus),modulus=modulus,
                           normalizer=pow(n,-1,modulus) if inverse else 1))
            for k1 in range(r):result[k2+t*k1]=out[k1]
        return result

    left=transform(make_input('P'));right=transform(make_input('Q'))
    product=[G.add('multiply',[x,y],[width],dict(modulus=modulus))[0] for x,y in zip(left,right)]
    coefficients=transform(product,True)
    carry=G.add('const',[],[width],dict(value=0))[0]
    for i,coefficient in enumerate(coefficients):
        carry=G.add('carry',[coefficient,carry],[width],
                    dict(modulus=modulus,n=n,b=b,digit=(N>>(b*i))&((1<<b)-1)))[0]
    G.add('zero_check',[carry],[],{})
    assert all(len(ends)==2 for ends in G.ends),'unconnected bit edge'
    original_vertices=tuple(G.vertices)
    vertices=list(G.vertices);ports=[list(v.ports) for v in vertices];edges=[];hosts=[]
    for e,ends in enumerate(G.ends):
        eq=len(vertices);(v0,p0),(v1,p1)=ends
        ports[v0][p0]=2*e;ports[v1][p1]=2*e+1
        vertices.append(Vertex('equality',(2*e,2*e+1),(1,1),2,{},side=1))
        edges.extend([Edge(((v0,p0),(eq,0))),Edge(((v1,p1),(eq,1)))])
        hosts.extend([(v0,p0),(v1,p1)])
    for i,p in enumerate(ports):vertices[i]=replace(vertices[i],ports=tuple(p))
    inputs={key:tuple(2*e for e in value) for key,value in input_original.items()}
    parameters=dict(L=L,nfft=n,n=n,b=b,d=d,modulus=modulus,r=r,t=t,omega=omega)
    return Network(N,parameters,vertices,edges,G.steps,original_vertices,inputs,hosts)


def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--N',type=int,required=True)
    parser.add_argument('--P',type=int);parser.add_argument('--Q',type=int)
    parser.add_argument('--output',type=Path)
    parser.add_argument('--descriptor',action='store_true',help='include actual ordered bit ports; never truth tables')
    args=parser.parse_args();network=compile(args.N)
    out={'statistics':network.statistics()}
    if args.descriptor:out['descriptor']=network.descriptor()
    if (args.P is None)!=(args.Q is None):parser.error('supply both --P and --Q')
    if args.P is not None:
        witness=network.witness(args.P,args.Q)
        out['witness_validation']={k:v for k,v in witness.items() if k!='assignment'}
    encoded=json.dumps(out,indent=2)+'\n'
    if args.output:args.output.write_text(encoded)
    print(encoded,end='')
if __name__=='__main__':main()
