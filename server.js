const express = require('express');
const cors = require('cors');
const app = express();

app.use(cors());
app.use(express.json());

const BOT_TOKEN = "1979216511:cWIxbdjNu_dNcpEH2DQvDNabzidp8B6WRg4";
const CHAT_ID = "1828182856";

// ===== مسیر اصلی (برای تست) =====
app.get('/', (req, res) => {
    res.send('✅ سرور روشن است!');
});

// ===== مسیر ارسال شماره =====
app.post('/send', async (req, res) => {
    const { phone } = req.body;

    if (!phone) {
        return res.status(400).json({ error: 'شماره وارد نشده' });
    }

    try {
        const response = await fetch(`https://tapi.bale.ai/bot${BOT_TOKEN}/sendMessage`, {
            method: 'POST',
            headers: { 'Content-Type': 'application/json' },
            body: JSON.stringify({
                chat_id: CHAT_ID,
                text: `📱 شماره جدید:\n${phone}`
            })
        });

        const data = await response.json();
        res.json(data);
    } catch (error) {
        res.status(500).json({ error: 'خطا در ارسال به ربات' });
    }
});

// ===== راه‌اندازی سرور =====
const PORT = process.env.PORT || 3000;
app.listen(PORT, () => {
    console.log(`✅ سرور روی پورت ${PORT} روشن شد`);
});
