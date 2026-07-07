const express = require('express');
const app = express();
const cors = require('cors');

app.use(cors());
app.use(express.json());

const BOT_TOKEN = "1979216511:cWIxbdjNu_dNcpEH2DQvDNabzidp8B6WRg4";
const CHAT_ID = "1828182856";

app.post('/send', async (req, res) => {
    const { phone } = req.body;
    if (!phone) return res.status(400).json({ error: 'شماره وارد نشده' });

    try {
        const response = await fetch(`https://tapi.bale.ai/bot${BOT_TOKEN}/sendMessage`, {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({
                chat_id: CHAT_ID,
                text: `📱 شماره جدید: ${phone}`
            })
        });
        const data = await response.json();
        res.json(data);
    } catch (error) {
        res.status(500).json({ error: 'خطا در ارسال' });
    }
});

app.listen(3000, () => console.log('✅ سرور روشن شد'));
