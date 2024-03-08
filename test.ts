type TamanhoString<T extends string> = T['length'] | 0;


const n: TamanhoString<'Olá'> = 100000;
