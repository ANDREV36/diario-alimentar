# Implementação da versão multiusuário

## Resumo

A versão entregue transforma o aplicativo em uma aplicação multiusuário compatível com GitHub/Render, preservando o diário alimentar, o perfil, o cálculo de metas e a hidratação. O ponto de entrada ativo é `app.py`.

## Funcionalidades implementadas

| Área | Implementação |
|---|---|
| Contas | Cadastro por e-mail e senha com validação mínima de oito caracteres. |
| Senhas | Hash com `hashlib.scrypt`; a senha original não é gravada. |
| Sessões | Cookie HTTP-only, expiração de 30 dias e token armazenado como HMAC no banco. |
| Isolamento | Perfil, metas, consumo, hidratação, favoritos, porções e alimentos personalizados usam `usuario_id`. |
| Migração | A primeira conta criada recebe os dados da versão single-user, se existirem. |
| Metas | Modo automático e modo manual persistente com retorno explícito ao cálculo do perfil. |
| Cadastro alimentar | Base SQLite compartilhada em leitura e alimentos personalizados privados no PostgreSQL. |
| Fotografia | Foto redimensionada no navegador, enviada ao backend, lida por modelo de visão, normalizada por porção e apresentada para conferência antes do salvamento. |
| Favoritos | Salvar e reutilizar alimentos frequentes. |
| Porções | Salvar nome e quantidade habitual e reutilizar no registro. |
| Histórico | Acumulado por período e gráfico diário em barras sem biblioteca externa. |
| Exportação | Download do diário em CSV. |
| Monitoramento | Rota `/health` com resposta `ok`. |
| Validação | Limites de idade, peso, altura, ritmo, metas, hidratação e quantidade consumida. |

## Configuração do Render

Use `pip install -r requirements.txt` como Build Command e `python app.py` como Start Command. Configure `DATABASE_URL`, `SESSION_SECRET` e, para habilitar a fotografia, `OPENAI_API_KEY`. `PORT` é fornecida automaticamente pelo Render; `VISION_MODEL` é opcional.

A chave de visão é usada somente no servidor. A fotografia é processada temporariamente, não é salva no disco do Render e não fica exposta no navegador depois do processamento.

## Testes realizados

Foram aprovados `python3 -m py_compile app.py`, validação de recursos obrigatórios, `node --check` no JavaScript embutido, teste de hash/verificação de senha e `git diff --check`. Também foi instalada localmente a mesma família de dependências do Render (`psycopg[binary]` e `openai`) para validar a importação dos módulos.

Não foi possível executar um teste de integração conectado ao PostgreSQL neste ambiente porque não há um servidor PostgreSQL local disponível. Por isso, a primeira validação real das tabelas e da migração deverá ser feita no PostgreSQL do Render. Recomenda-se criar um backup antes do primeiro deploy sobre dados existentes.

## Itens que dependem do serviço de produção

Backups automáticos devem ser habilitados conforme o plano e os recursos do PostgreSQL no Render; o aplicativo não expõe uma rota pública de backup, por segurança. Recuperação de senha por e-mail e confirmação de e-mail exigem a configuração posterior de um provedor de envio de mensagens e não foram ativadas nesta versão.

As metas são estimativas de acompanhamento e não substituem avaliação individual de médico ou nutricionista.
